// AMD's lane. A Radeon has no migrating managed memory, so the corpus is
// host memory and gpu_vram its twin on the device, which a ! copies in and
// out: every Loc is an index, and the host never runs during a device turn.
static Corpus gpu_vram;

// comgr scans every PATH entry for ld.lld (then uses its own): under WSL
// (/dev/dxg) the /mnt/ entries cost ~0.5 s. So setup runs without them and
// PATH comes back (drop false) once the module is loaded or no device is
// found; the drop runs before any thread, and glibc's in-place setenv never
// frees a string a HIP thread's getenv may hold.
static char* gpu_env_path;
static void gpu_env(bool drop) {
  const char* p = getenv("PATH");
  if (drop && p != NULL && access("/dev/dxg", F_OK) == 0) {
    gpu_env_path = strdup(p);
    setenv("PATH", "/usr/bin", 1);
  } else if (!drop && gpu_env_path != NULL) {
    setenv("PATH", gpu_env_path, 1);
    free(gpu_env_path);
    gpu_env_path = NULL;
  }
}

static bool gpu_probe(void) {
  int n = 0;
  gpu_env(true);
  bool ok = hipInit(0) == hipSuccess && hipGetDeviceCount(&n) == hipSuccess
    && n > 0 && hipSetDevice(gpu_dev) == hipSuccess;
  if (!ok) {
    gpu_env(false);
  }
  return ok;
}

// The twin's heap is lazy, in GPU_CHUNKs (modelled and proven in
// demos/proof_gpu_coherence). An enter uploads the dirty chunks, then clean:
// read only. A leave makes stale (no access) each chunk the device marked
// (see Twin) and each from the ceiling (the chunk of H_TWIN_HI) up; the
// rest keep their state. A host touch downloads a stale chunk, clean;
// a write makes a clean one dirty, read-write. The bump cannot say what the
// host wrote (freed slots are rewritten under it). A fault fills a chunk
// through gpu_alias, a second mapping, while it still traps. Prefetch: a
// leave also fetches, in runs, what the host touched since the last leave
// of the same bang (its key): current, trapping, opened with no copy. A
// key's first leave fetches nothing. BEND_GPU_PREFETCH=0 fetches nothing, =2 all.
#define GPU_CHUNK   (1ull << 18)
#define GPU_DIRTY   0
#define GPU_CLEAN   1
#define GPU_STALE   2  // stale and fetched trap
#define GPU_FETCHED 3
#define GPU_KEYS    8
#define GPU_BIT(m, c) ((m)[(c) >> 6] >> ((c) & 63) & 1)
static u8*   gpu_state;       // a GPU_ state a tracked chunk; calloc is dirty
static char* gpu_alias;
static u64   gpu_lo, gpu_hi;  // the tracked bytes of the corpus, whole chunks
static u32*  gpu_lock;        // a tracked chunk's lock (see gpu_fault)
static u8*   gpu_todo;        // the leave's plan (gpu_plan), a tracked chunk
static u32   gpu_pf, gpu_key;   // BEND_GPU_PREFETCH; the entered bang's fid
static u64   gpu_words;         // a chunk bitmap's u64s
static u64*  gpu_cur;           // the chunks the host touched since the leave
typedef struct {
  u32 key;
  u64 last, *hist;  // its last leave; its last interval's touches
} GpuKey;
static GpuKey  gpu_keys[GPU_KEYS];  // the least recently left goes first
static GpuKey* gpu_at;              // the key whose leave opened the interval
// the enter's H_TWIN_HI in bytes, clamped; its chunk: the ceiling
static u64   gpu_twhi, gpu_ceil;
static u32*  gpu_mk;    // the leave's copy of the map, a tracked chunk each
static bool  gpu_check; // BEND_GPU_CHECK=1: K0, K1, K2 (see gpu_k)
static char* gpu_snap;  // the check's copy of [gpu_lo, gpu_twhi) at the enter
static u64   corpus_size;  // the Corpus section's (a tentative definition)
static u64   gpu_snap_cap;
_Static_assert(GPU_CHUNK == 8ull << TWIN_LOG, "a map chunk is a GPU_CHUNK");

// BEND_GPU_STATS=1: at exit, what the turns cost, by region and way
static bool gpu_stat;
// 0 header, 1 rings, 2 heap, 3 banks
static u32  gpu_part;
static u64  gpu_turns, gpu_dev_ns;
static u64  gpu_calls[4][2], gpu_bytes[4][2], gpu_ns[4][2];
// gpu_pin's pieces' ends, ascending; gpu_paged: bytes paged since the last
#define GPU_PIN_GRAIN   (32ull << 20)
#define GPU_PIN_PAYBACK 4
static u64* gpu_pins;
static u64  gpu_npin, gpu_pin_hi, gpu_paged;
static bool gpu_nopin;
static u64  io_tick(void);

// atomic: faults on different chunks tally at once
#define GPU_ADD(x, v) __atomic_fetch_add(&(x), (v), __ATOMIC_RELAXED)
static void gpu_tally(u32 k, bool up, u64 bytes, u64 t0) {
  GPU_ADD(gpu_calls[k][up], 1);
  GPU_ADD(gpu_bytes[k][up], bytes);
  GPU_ADD(gpu_ns[k][up], io_tick() - t0);
}

static void gpu_stats(void) {
  static const char* part[4] = { "header", "rings ", "heap  ", "banks " };
  fprintf(stderr, "bend: hip %llu turns, passes %llu us\n",
    (unsigned long long)gpu_turns, (unsigned long long)(gpu_dev_ns / 1000));
  for (u32 k = 0; k < 4; k += 1) {
    fprintf(stderr, "bend: hip   %s", part[k]);
    for (u32 up = 2; up-- > 0;) {
      fprintf(stderr, " %s %llu calls %llu KB %llu us%s", up ? "up" : "down",
        (unsigned long long)gpu_calls[k][up],
        (unsigned long long)(gpu_bytes[k][up] >> 10),
        (unsigned long long)(gpu_ns[k][up] / 1000), up ? "," : "\n");
    }
  }
}

// a fresh mapping is zero; the twin is zeroed as corpus_setup does CUDA's
static Corpus gpu_map(u64 bytes) {
  void* v  = NULL;
  int   fd = memfd_create("bend-corpus", 0);
  if (fd < 0 || ftruncate(fd, (off_t)bytes) != 0) {
    err_fail("corpus reservation failed");
  }
  void* p = mmap(NULL, bytes, PROT_READ | PROT_WRITE,
    MAP_SHARED | MAP_NORESERVE, fd, 0);
  void* a = mmap(NULL, bytes, PROT_READ | PROT_WRITE,
    MAP_SHARED | MAP_NORESERVE, fd, 0);
  close(fd);
  if (p == MAP_FAILED || a == MAP_FAILED) {
    err_fail("corpus reservation failed");
  }
  if (hipMalloc(&v, bytes) != hipSuccess
    || hipMemset(v, 0, STAK_OFF * 8) != hipSuccess
    || hipDeviceSynchronize() != hipSuccess) {
    err_fail("device corpus reservation failed");
  }
  gpu_vram  = (Corpus)v;
  gpu_alias = (char*)a;
  return (Corpus)p;
}

static bool gpu_make(const char* path) {
  hipDeviceProp_t props;
  if (hipGetDeviceProperties(&props, gpu_dev) != hipSuccess) {
    err_fail("cannot compile the HIP library");
  }
  char arch[300];
  char bag[24];
  snprintf(arch, sizeof arch, "--offload-arch=%s", props.gcnArchName);
  snprintf(bag, sizeof bag, "-DCUBE_LOG=%u", CUBE_LOG);
  const char* opts[] = { arch, bag, "-O3", "-ffp-contract=off" };
  hiprtcProgram prog;
  if (hiprtcCreateProgram(&prog, BEND_SRC, "bend.hip", 0, NULL, NULL)
    != HIPRTC_SUCCESS) {
    err_fail("cannot compile the HIP library");
  }
  if (hiprtcCompileProgram(prog, 4, opts) != HIPRTC_SUCCESS) {
    size_t n = 0;
    hiprtcGetProgramLogSize(prog, &n);
    char* log = calloc(n + 1, 1);
    if (log != NULL && hiprtcGetProgramLog(prog, log) == HIPRTC_SUCCESS) {
      fprintf(stderr, "%s\n", log);
    }
    err_fail("cannot compile the HIP library");
  }
  size_t len = 0;
  hiprtcGetCodeSize(prog, &len);
  char* bin = malloc(len);
  if (bin == NULL || hiprtcGetCode(prog, bin) != HIPRTC_SUCCESS) {
    err_fail("cannot load the HIP library");
  }
  hiprtcDestroyProgram(&prog);
  u64   key = gpu_hash();
  FILE* out = path == NULL ? NULL : fopen(path, "wb");
  bool  ok  = out != NULL && fwrite(&key, 8, 1, out) == 1
    && fwrite(bin, 1, len, out) == len && fclose(out) == 0;
  if (hipModuleLoadData(&gpu_lib, bin) != hipSuccess) {
    err_fail("cannot load the HIP library");
  }
  free(bin);
  gpu_env(false);
  return path == NULL || ok;
}

// the twin is reserved whole: 1 GB, and --gpu 2GB asks for more
static u64 gpu_span(void) {
  return 1ull << 30;
}

static void gpu_load(u64 bytes) {
  const char* path = gpu_path();
  int         fd   = open(path, O_RDONLY);
  struct stat st   = { 0 };
  u64         key  = 0;
  char*       bin  = fd < 0 || fstat(fd, &st) != 0 || st.st_size <= 8 ? NULL
    : mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  if (bin != NULL && bin != MAP_FAILED) {
    memcpy(&key, bin, 8);
  }
  if (key != gpu_hash()
    || hipModuleLoadData(&gpu_lib, bin + 8) != hipSuccess) {
    gpu_note(path);
    gpu_make(path);
  }
  if (hipModuleGetFunction(&gpu_pso, gpu_lib, "bend_dev") != hipSuccess) {
    err_fail("cannot load the GPU program");
  }
  gpu_env(false);
  const char* pf = getenv("BEND_GPU_PREFETCH");
  gpu_pf   = pf == NULL ? 1 : (u32)atoi(pf);
  gpu_stat = getenv("BEND_GPU_STATS") != NULL;
  gpu_check = getenv("BEND_GPU_CHECK") != NULL
    && strcmp(getenv("BEND_GPU_CHECK"), "0") != 0;
  if (gpu_stat) {
    atexit(gpu_stats);
  }
}

// Batching: a HIP call costs ~0.1 ms under WSL2 whatever its size, so a
// copy of up to GPU_STAGE_MAX is a piece of a flush, all moved by one
// gpu_move_dev: zero-copy in a registered piece of gpu_alias, else through
// a pinned buffer that a copy up fills at the call and a wait spreads down
// into gpu_alias. So a copy up is read when the kernel runs, a copy down
// lands at the wait. The buffer empties only at a wait (a flushed piece
// stays put until run) and grows up to GPU_STAGE_CAP. A pass waits at its
// end; a leave once what it reads first is down, and at its end. Batched, BEND_GPU_STATS times a copy's staging.
#define GPU_STAGE_MAX (16ull << 20)
#define GPU_STAGE_CAP (32ull << 20)
#define GPU_PIECE     2048
typedef struct {
  char* h;
  u64   s, n;
} GpuOut;
static u64*          gpu_at_buf;   // the pinned buffer
static u64*          gpu_at_dev;   // as the device sees it
static u64           gpu_cap;      // its words
static u64           gpu_used;     // its words in use, since the last wait
static u64*          gpu_tab;      // the pieces, 3 words each
static u32           gpu_tabs;
static GpuOut*       gpu_outs;     // the downs to spread at a wait
static u32           gpu_nout;
static char**        gpu_pin_dev;  // a registered piece's start, the device's
static hipFunction_t gpu_mover;

// a kernel's launch, its arguments packed as the kernel lays them
static void gpu_launch(hipFunction_t f, u32 gx, u32 gy, u32 bx, u32 by,
  u32 shm, void* args, size_t len) {
  void* cfg[] = { HIP_LAUNCH_PARAM_BUFFER_POINTER, args,
    HIP_LAUNCH_PARAM_BUFFER_SIZE, &len, HIP_LAUNCH_PARAM_END };
  if (hipModuleLaunchKernel(f, gx, gy, 1, bx, by, 1, shm, NULL, NULL, cfg)
    != hipSuccess) {
    err_fail("device launch failed");
  }
}

static void gpu_flush(bool wait) {
  if (gpu_tabs != 0) {
    u64* t = gpu_at_buf + gpu_used;
    memcpy(t, gpu_tab, gpu_tabs * 24);
    struct { Corpus mem; u64* tab; u32 n; } args = { gpu_vram,
      gpu_at_dev + gpu_used, gpu_tabs };
    gpu_launch(gpu_mover, gpu_tabs < 1024 ? gpu_tabs : 1024, 1, 256, 1, 0,
      &args, sizeof args);
    gpu_used += 3 * gpu_tabs;
    gpu_tabs  = 0;
  }
  if (wait && gpu_used != 0) {
    if (hipDeviceSynchronize() != hipSuccess) {
      err_fail("device fault");
    }
    for (u32 i = 0; i < gpu_nout; i += 1) {
      memcpy(gpu_outs[i].h, gpu_at_buf + gpu_outs[i].s, gpu_outs[i].n);
    }
    gpu_nout = 0;
    gpu_used = 0;
  }
}

// n words more of the buffer and k pieces more: the word they start at
static u64 gpu_room(u64 n, u64 k) {
  if (gpu_used + n + 3 * (gpu_tabs + k) > gpu_cap) {
    gpu_flush(true);
    u64   w = gpu_cap == 0 ? 1ull << 19
      : gpu_cap < GPU_STAGE_CAP / 8 ? 2 * gpu_cap : gpu_cap;
    void* d = NULL;
    while (w < n + 3 * k) {
      w *= 2;
    }
    if (w == gpu_cap) {
      gpu_used += n;
      return gpu_used - n;
    }
    if (hipHostFree(gpu_at_buf) != hipSuccess
      || hipHostMalloc((void**)&gpu_at_buf, w * 8, 0) != hipSuccess
      || hipHostGetDevicePointer(&d, gpu_at_buf, 0) != hipSuccess
      || (gpu_mover == NULL && hipModuleGetFunction(&gpu_mover, gpu_lib,
        "gpu_move_dev") != hipSuccess)
      || (gpu_tab = realloc(gpu_tab, w * 8)) == NULL
      || (gpu_outs = realloc(gpu_outs, w * 8)) == NULL) {
      err_fail("the staging buffer failed");
    }
    gpu_at_dev = (u64*)d;
    gpu_cap    = w;
  }
  gpu_used += n;
  return gpu_used - n;
}

// the twin's bytes [a, b) to or from h, the host's, or zero-copy from x,
// the device's address of them in a registered piece
static void gpu_stage(u64 a, u64 b, bool up, char* h, char* x) {
  u64 n = (b - a) / 8;
  u64 k = (n + GPU_PIECE - 1) / GPU_PIECE;
  u64 s = gpu_room(x != NULL ? 0 : n, k);
  if (x == NULL && up) {
    memcpy(gpu_at_buf + s, h, b - a);
  } else if (x == NULL) {
    gpu_outs[gpu_nout++] = (GpuOut){ h, s, b - a };
  }
  x = x != NULL ? x : (char*)(gpu_at_dev + s);
  for (u64 i = 0; i < n; i += GPU_PIECE) {
    u64* t = gpu_tab + 3 * gpu_tabs++;
    t[0] = a / 8 + i;
    t[1] = (u64)(uintptr_t)(x + i * 8) | (u64)up << 63;
    t[2] = n - i < GPU_PIECE ? n - i : GPU_PIECE;
  }
}

// The corpus's bytes [a, b) to or from the device, cut at the pieces'
// edges (a copy across one fails); the host side is gpu_alias in a piece
// or when al, else CORPUS
static bool gpu_move(u64 a, u64 b, bool up, bool al) {
  bool st = b - a <= GPU_STAGE_MAX;
  if (!st) {  // after the pieces before it
    gpu_flush(false);
  }
  while (a < b) {
    u64 e = b, i = 0;
    if (a < gpu_pin_hi) {  // the next edge above a
      while (gpu_pins[i] <= a) {
        i += 1;
      }
      e = a < gpu_lo ? gpu_lo : gpu_pins[i];
      e = e < b ? e : b;
    }
    char* h = al || (a >= gpu_lo && a < gpu_pin_hi) ? gpu_alias
      : (char*)CORPUS;
    if (a >= gpu_pin_hi && a >= gpu_lo && a < gpu_hi) {
      GPU_ADD(gpu_paged, e - a);
    }
    if (st) {
      char* x = a >= gpu_lo && a < gpu_pin_hi ? gpu_pin_dev[i]
        + (a - (i != 0 ? gpu_pins[i - 1] : gpu_lo)) : NULL;
      gpu_stage(a, e, up, gpu_alias + a, x);
    } else if (hipMemcpy(up ? (char*)gpu_vram + a : h + a,
      up ? h + a : (char*)gpu_vram + a, e - a,
      up ? hipMemcpyHostToDevice : hipMemcpyDeviceToHost) != hipSuccess) {
      return false;
    }
    a = e;
  }
  return true;
}

static void gpu_copy(u64 lo, u64 hi, bool up) {
  if (hi <= lo) {
    return;
  }
  u64 t0 = gpu_stat ? io_tick() : 0;
  if (!gpu_move(lo * 8, hi * 8, up, false)) {
    err_fail("corpus copy failed");
  }
  if (gpu_stat) {
    gpu_tally(gpu_part, up, (hi - lo) * 8, t0);
  }
}

// the enter's mend on the twin: from, each ring's put at the leave, goes up
static void gpu_mend(const u32* from) {
  static hipFunction_t pso;
  if (pso == NULL && hipModuleGetFunction(&pso, gpu_lib, "ring_mend_dev")
    != hipSuccess) {
    err_fail("cannot load the ring kernel");
  }
  u64  s  = gpu_room(LANES / 2, 0);  // the rings' pieces go first
  u32* at = (u32*)(gpu_at_dev + s);
  memcpy(gpu_at_buf + s, from, LANES * 4);
  gpu_flush(false);
  struct { Corpus mem; u32* from; } args = { gpu_vram, at };
  gpu_launch(pso, CUBE_G, 1, CUBE_T, 1, 0, &args, sizeof args);
}

// The free-list rows stay in VRAM (the host keeps ALC[]). Of the rings the
// counters go, and the slot rows some ring has live; then the other side's
// mend (see ring_mend) from each ring's put at the last sync.
static void gpu_rings(bool up) {
  static u8   live[1u << 17];  // RING_LEN at its widest (CUBE_LOG = 0)
  static u32* from;            // a zero put, as the corpus starts
  Corpus      H = CORPUS;
  if (up) {  // down, gpu_sync brought them
    gpu_copy(RING_OFF + RING_LEN * LANES, RING_OFF + (RING_LEN + 2) * LANES,
      true);
  }
  memset(live, 0, RING_LEN);
  for (u32 r = 0; r < LANES; r += 1) {
    u32 get = a32_load(ring_get(H, r));
    u32 n   = a32_load(ring_put(H, r)) - get;
    n = n < RING_LEN ? n : (u32)RING_LEN;
    for (u32 i = 0; i < n; i += 1) {
      live[(get + i) & (RING_LEN - 1)] = 1;
    }
  }
  for (u64 w = 0; w < RING_LEN; w += 1) {
    u64 lo = w;
    while (w < RING_LEN && live[w]) {
      w += 1;
    }
    gpu_copy(RING_OFF + lo * LANES, RING_OFF + w * LANES, up);
  }
  u64 n = 0;
  if (from == NULL && (from = calloc(LANES, 4)) == NULL) {
    err_fail("corpus reservation failed");
  }
  for (u32 r = 0; r < LANES; r += 1) {
    u32 lo = 0;
    n += up ? ring_taken(H, r, from[r], &lo) : ring_mend(H, r, from[r]);
  }
  if (up && n != 0) {
    gpu_mend(from);
  }
  for (u32 r = 0; r < LANES; r += 1) {
    from[r] = a32_load(ring_put(H, r));
  }
}

// The leave's plan for chunk c < n: bit 1, invalidate (marked, or at or
// above the ceiling t); bit 2, fetch (wanted, and invalidated or stale)
static void gpu_plan(u64 n, u64 t, const u8* st, const u32* mk,
  const u64* want, u32 pf, u8* out) {
  for (u64 c = 0; c < n; c += 1) {
    bool i = c >= t || mk[c] != 0;
    bool w = pf == 2 || (pf != 0 && GPU_BIT(want, c));
    out[c] = (u8)(i | (w && (i || st[c] == GPU_STALE)) << 1);
  }
}

// At a leave: the key's slot (a new key takes the least recently left,
// empty); I goes stale, no access; then P comes down in runs, fetched.
static void gpu_fetch(u64 n) {
  GpuKey* k = gpu_keys;
  for (GpuKey* s = gpu_keys; s < gpu_keys + GPU_KEYS; s += 1) {
    if (s->hist != NULL && s->key == gpu_key) {
      k = s;
      break;
    }
    k = s->last < k->last ? s : k;
  }
  u64 nt = (gpu_hi - gpu_lo) / GPU_CHUNK;
  if (k->hist == NULL || k->key != gpu_key) {
    u64* h = k->hist != NULL ? k->hist : calloc(gpu_words, 8);
    if (h == NULL) {
      err_fail("corpus reservation failed");
    }
    memset(h, 0, gpu_words * 8);
    *k = (GpuKey){ .key = gpu_key, .hist = h };
  }
  k->last = gpu_turns;
  gpu_at  = k;
  n = n < nt ? n : nt;
  gpu_plan(n, gpu_ceil, gpu_state, gpu_mk, k->hist, gpu_pf, gpu_todo);
  for (u64 c = 0; c < n; c += 1) {
    u64 lo = c;
    for (; c < n && gpu_todo[c] & 1; c += 1) {
      gpu_state[c] = GPU_STALE;
    }
    if (c > lo && mprotect((char*)CORPUS + gpu_lo + lo * GPU_CHUNK,
      (c - lo) * GPU_CHUNK, PROT_NONE) != 0) {
      err_fail("corpus protection failed");
    }
  }
  for (u64 c = 0; c < n; c += 1) {
    u64 lo = c, at = gpu_lo + c * GPU_CHUNK;
    while (c < n && gpu_todo[c] & 2) {
      c += 1;
    }
    if (c > lo) {
      if (!gpu_move(at, at + (c - lo) * GPU_CHUNK, false, true)) {
        err_fail("corpus copy failed");
      }
      memset(gpu_state + lo, GPU_FETCHED, c - lo);
    }
  }
}

// A chunk's lock: a waiter spins on a load, with a pause, not on the swap
static void gpu_hold(u32* l) {
  while (__atomic_exchange_n(l, 1, __ATOMIC_ACQUIRE)) {
    while (__atomic_load_n(l, __ATOMIC_RELAXED)) {
#ifdef __x86_64__
      __builtin_ia32_pause();
#endif
    }
  }
}

// Under chunk c's lock: the host touched it (the bitmap is shared: atomic)
static void gpu_touch(u64 c) {
  if (gpu_at != NULL) {
    __atomic_fetch_or(&gpu_cur[c >> 6], 1ull << (c & 63), __ATOMIC_RELAXED);
  }
}

// At an enter the interval's touches become the history of the key whose
// leave opened it (a chunk kept valid across the leave is not in it)
static void gpu_publish(void) {
  if (gpu_at != NULL) {
    u64* h = gpu_at->hist;
    gpu_at->hist = gpu_cur;
    gpu_cur      = h;
    memset(gpu_cur, 0, gpu_words * 8);
  }
}

// BEND_GPU_CHECK=1, chunk c below byte to: K0, after the enter's uploads, a
// chunk not stale holds the device's bytes; at the leave, K1, an unmarked
// chunk under H_TWIN_HI holds its bytes at the enter (a snapshot), and K2,
// an unmarked one under the ceiling, not stale, the host's
static void gpu_k(u64 c, u64 to, bool k1, bool host) {
  static u64 *d, *x;
  u64 at  = gpu_lo + c * GPU_CHUNK;
  u64 len = to - at < GPU_CHUNK ? to - at : GPU_CHUNK;
  if ((d == NULL && (d = malloc(GPU_CHUNK)) == NULL)
    || (x == NULL && (x = malloc(GPU_CHUNK)) == NULL)
    || hipMemcpy(d, (char*)gpu_vram + at, len, hipMemcpyDeviceToHost)
    || (k1 && hipMemcpy(x, gpu_snap + (at - gpu_lo), len,
      hipMemcpyDeviceToHost))) {
    err_fail("the GPU check's copy failed");
  }
  for (u32 k = 0; k < 2; k += 1) {
    const u64* r = k == 0 ? (k1 ? x : NULL)
      : host ? (const u64*)(gpu_alias + at) : NULL;
    for (u64 w = 0; r != NULL && w < len / 8; w += 1) {
      if (d[w] != r[w]) {
        fprintf(stderr, "bend: GPU check %s: word %llu (chunk %llu, state"
          " %u%s) is %016llx (tag %u) on the device, %016llx (tag %u) %s\n",
          k == 0 ? "K1" : k1 ? "K2" : "K0", (unsigned long long)(at / 8 + w),
          (unsigned long long)c, gpu_state[c], k1 ? ", unmarked" : "",
          (unsigned long long)d[w], (u32)(d[w] >> 56),
          (unsigned long long)r[w], (u32)(r[w] >> 56),
          k == 0 ? "at the enter" : "on the host");
        err_fail("GPU check failed");
      }
    }
  }
}

// Pinned, the alias copies at ~20 GB/s, not ~4, but registering costs
// ~0.6 to 0.9 ms a MB: rent or buy. gpu_heap grows the registered prefix
// to cover to, as a new piece (at least a quarter of what is registered,
// in GPU_PIN_GRAINs, edges on chunks), once the bytes copied pageable
// since the last piece reach GPU_PIN_PAYBACK times its size. Past half of
// MemAvailable, or on a failure, it stops with a warning.
static void gpu_pin(u64 to) {
  u64 at = gpu_npin != 0 ? gpu_pin_hi : gpu_lo;
  u64 hi = to > at + (at - gpu_lo) / 4 ? to : at + (at - gpu_lo) / 4;
  hi = gpu_lo + ((hi - gpu_lo + GPU_PIN_GRAIN - 1) & ~(GPU_PIN_GRAIN - 1));
  hi = hi < gpu_hi ? hi : gpu_hi;
  if (gpu_nopin || to <= at || hi <= at
    || gpu_paged < GPU_PIN_PAYBACK * (hi - at)) {
    return;
  }
  char    mi[512] = { 0 };
  int     fd = open("/proc/meminfo", O_RDONLY);
  ssize_t r  = fd < 0 ? -1 : read(fd, mi, sizeof mi - 1);
  char*   av = r > 0 ? strstr(mi, "MemAvailable:") : NULL;
  u64     kb = av == NULL ? 0 : strtoull(av + 13, NULL, 10);
  bool    big = (hi - gpu_lo) >> 10 > (kb + ((at - gpu_lo) >> 10)) / 2;
  if (fd >= 0) {
    close(fd);
  }
  void* d  = NULL;
  bool  ok = !big && hipHostRegister(gpu_alias + at, hi - at,
    hipHostRegisterMapped) == hipSuccess;
  if (ok && hipHostGetDevicePointer(&d, gpu_alias + at, 0) != hipSuccess) {
    (void)hipHostUnregister(gpu_alias + at);
    ok = false;
  }
  if (!ok) {
    fprintf(stderr, "bend: hip pin %s at %llu of %llu MB (%llu MB"
      " available); the rest stays pageable\n", big ? "stopped" : "failed",
      (unsigned long long)((at - gpu_lo) >> 20),
      (unsigned long long)((hi - gpu_lo) >> 20),
      (unsigned long long)(kb >> 10));
    gpu_nopin = true;
    return;
  }
  if (hipDeviceSynchronize() != hipSuccess) {
    err_fail("device fault");
  }
  gpu_pin_dev[gpu_npin] = (char*)d;
  gpu_pins[gpu_npin++]  = hi;
  gpu_pin_hi  = hi;
  gpu_paged   = 0;
}

// The static image and the heap up to the word end. The tracked chunks are
// the whole ones within the heap; what lies outside them goes eagerly.
// way: 0 a leave, 1 an enter, 2 gpu_show's upload
static void gpu_heap(u64 end, u32 way) {
  Corpus H  = CORPUS;
  bool   up = way != 0;
  u64    m  = H[H_TWIN_MAP] * 8;
  if (gpu_state == NULL) {
    u64 cap = a32_load(a32_at(H, H_CAP));
    gpu_lo = (HEAP_OFF * 8 + GPU_CHUNK - 1) & ~(GPU_CHUNK - 1);
    gpu_hi = ((HEAP_OFF + (cap << PAGE_BITS)) * 8) & ~(GPU_CHUNK - 1);
    gpu_hi = gpu_hi < gpu_lo ? gpu_lo : gpu_hi;
    gpu_words = ((gpu_hi - gpu_lo) / GPU_CHUNK + 64) / 64;
    gpu_state = calloc((gpu_hi - gpu_lo) / GPU_CHUNK + 1, 1);
    gpu_lock  = calloc((gpu_hi - gpu_lo) / GPU_CHUNK + 1, 4);
    gpu_cur   = calloc(gpu_words, 8);
    gpu_mk    = calloc((gpu_hi - gpu_lo) / GPU_CHUNK + 1, 4);
    gpu_todo  = calloc((gpu_hi - gpu_lo) / GPU_CHUNK + 1, 1);
    // the twin's map is zero from here: gpu_map zeroes only below STAK_OFF
    if (gpu_state == NULL || gpu_lock == NULL || gpu_cur == NULL
      || gpu_mk == NULL || gpu_todo == NULL
      || gpu_hi / GPU_CHUNK > 2 * TWIN_MAPW(corpus_size / 8)
      || hipMemset((char*)gpu_vram + m, 0, TWIN_MAPW(corpus_size / 8) * 8)
      != hipSuccess) {
      err_fail("corpus reservation failed");
    }
    gpu_pins    = calloc((gpu_hi - gpu_lo) / GPU_PIN_GRAIN + 2, 8);
    gpu_pin_dev = calloc((gpu_hi - gpu_lo) / GPU_PIN_GRAIN + 2, 8);
    if (gpu_pins == NULL || gpu_pin_dev == NULL) {
      err_fail("corpus reservation failed");
    }
  }
  u64 e  = end * 8;
  u64 te = e < gpu_lo ? gpu_lo : e > gpu_hi ? gpu_hi
    : (e + GPU_CHUNK - 1) & ~(GPU_CHUNK - 1);
  gpu_copy(STAT_OFF, (e < gpu_lo ? e : gpu_lo) / 8, up);
  if (e > gpu_hi) {
    gpu_copy(gpu_hi / 8, end, up);
  }
  u64 n = (te - gpu_lo) / GPU_CHUNK;
  gpu_pin(te);
  if (way == 1) {
    u64 tw = H[H_TWIN_HI] * 8;
    gpu_twhi = tw < gpu_lo ? gpu_lo : tw > gpu_hi ? gpu_hi : tw;
    gpu_ceil = (gpu_twhi - gpu_lo) / GPU_CHUNK;
  }
  for (u64 c = 0; up && c < n;) {
    while (c < n && gpu_state[c] != GPU_DIRTY) {
      c += 1;
    }
    u64 lo = c;
    while (c < n && gpu_state[c] == GPU_DIRTY) {
      c += 1;
    }
    u64 hi = c;
    gpu_copy((gpu_lo + lo * GPU_CHUNK) / 8, (gpu_lo + hi * GPU_CHUNK) / 8, up);
    // clean, read only: left dirty it would go up every turn
    if (way == 1 && hi > lo) {
      if (mprotect((char*)H + gpu_lo + lo * GPU_CHUNK, (hi - lo) * GPU_CHUNK,
        PROT_READ) != 0) {
        err_fail("corpus protection failed");
      }
      memset(gpu_state + lo, GPU_CLEAN, hi - lo);
    }
    c = hi;
  }
  if (way == 1 && gpu_check) {
    gpu_flush(true);
    for (u64 c = 0; c < n; c += 1) {
      if (gpu_state[c] != GPU_STALE) {
        gpu_k(c, gpu_hi, false, true);
      }
    }
    u64 len = gpu_twhi - gpu_lo;
    if (len > gpu_snap_cap && (hipFree(gpu_snap) != hipSuccess
      || hipMalloc((void**)&gpu_snap, len) != hipSuccess)) {
      err_fail("the GPU check's snapshot does not fit in device memory");
    }
    gpu_snap_cap = len > gpu_snap_cap ? len : gpu_snap_cap;
    if (hipMemcpy(gpu_snap, (char*)gpu_vram + gpu_lo, len,
      hipMemcpyDeviceToDevice) != hipSuccess) {
      err_fail("the GPU check's copy failed");
    }
  }
  // Plain stores, no lock: no host thread runs during a turn (see gpu_fault)
  if (!up) {
    // the marks of the tracked chunks, by absolute chunk in the map
    memcpy(gpu_mk, gpu_alias + m + gpu_lo / GPU_CHUNK * 4, n * 4);
    for (u64 c = 0; gpu_check && gpu_lo + c * GPU_CHUNK < gpu_twhi; c += 1) {
      if (!gpu_mk[c]) {
        gpu_k(c, gpu_twhi, true, c < gpu_ceil && gpu_state[c] != GPU_STALE);
      }
    }
    gpu_fetch(n);
    // the whole map (4 bytes a chunk): a mark may run past H_TWIN_HI
    if (hipMemsetAsync((char*)gpu_vram + m, 0, TWIN_MAPW(corpus_size / 8)
      * 8, NULL) != hipSuccess) {
      err_fail("corpus copy failed");
    }
  }
}

// Fetched: open with no copy (used once). Stale: download through gpu_alias
// (the section touches no corpus page, so it cannot fault into its own
// lock). Either way a write opens read-write, dirty, else read only, clean,
// under the chunk's lock. Clean and a write: read-write, then dirty, with
// no lock (no bytes move). Anything else was served by another thread.
// Unlocked, this needs (main.bend's Ok): no host thread touches the corpus
// from gpu_enter to the first pass's wait, in gpu_leave or in gpu_show, and
// the uploader sees the flags and bytes through the pool's barrier
// (pool_done, released in pool_work, acquired in pool_turn).
static bool gpu_fault(void* addr, u32 wr) {
  u64 off = (u64)((char*)addr - (char*)CORPUS);
  if (gpu_state == NULL || (char*)addr < (char*)CORPUS || off < gpu_lo
    || off >= gpu_hi) {
    return false;
  }
  u64  c  = (off - gpu_lo) / GPU_CHUNK;
  u64  at = gpu_lo + c * GPU_CHUNK;
  u8*  st = &gpu_state[c];
  u8   s  = __atomic_load_n(st, __ATOMIC_ACQUIRE);
  bool ok = true;
  if (s == GPU_CLEAN && wr) {
    ok = mprotect((char*)CORPUS + at, GPU_CHUNK, PROT_READ | PROT_WRITE) == 0;
    if (ok) {
      __atomic_store_n(st, GPU_DIRTY, __ATOMIC_RELEASE);
    }
    return ok;
  }
  if (s == GPU_FETCHED) {
    gpu_hold(&gpu_lock[c]);
    if (__atomic_load_n(st, __ATOMIC_RELAXED) == GPU_FETCHED) {
      ok = mprotect((char*)CORPUS + at, GPU_CHUNK,
        wr == 1 ? PROT_READ | PROT_WRITE : PROT_READ) == 0;
      if (ok) {
        __atomic_store_n(st, wr == 1 ? GPU_DIRTY : GPU_CLEAN,
          __ATOMIC_RELEASE);
        gpu_touch(c);
      }
    }
    UNLOCK(gpu_lock[c]);
    return ok;
  }
  if (s == GPU_STALE) {
    gpu_hold(&gpu_lock[c]);
    s = __atomic_load_n(st, __ATOMIC_RELAXED);
    if (s == GPU_STALE) {
      u64 t0 = gpu_stat ? io_tick() : 0;
      u8  to = wr == 1 ? GPU_DIRTY : GPU_CLEAN;
      if (at >= gpu_pin_hi) {
        GPU_ADD(gpu_paged, GPU_CHUNK);
      }
      ok = hipMemcpy(gpu_alias + at, (char*)gpu_vram + at, GPU_CHUNK,
        hipMemcpyDeviceToHost) == hipSuccess
        && mprotect((char*)CORPUS + at, GPU_CHUNK,
          wr == 1 ? PROT_READ | PROT_WRITE : PROT_READ) == 0;
      __atomic_store_n(st, ok ? to : GPU_STALE, __ATOMIC_RELEASE);
      if (ok) {
        gpu_touch(c);
      }
      if (gpu_stat) {
        gpu_tally(2, false, GPU_CHUNK, t0);
      }
    }
    UNLOCK(gpu_lock[c]);
  }
  return ok;
}

// what a turn can touch, but the lanes' stacks; down, the header leads
static void gpu_sync(bool up) {
  Corpus H = CORPUS;
  gpu_turns += up;
  if (up) {
    gpu_publish();
    H[H_TWIN_HI] = HEAP_OFF + ((u64)a32_load(a32_at(H, H_BUMP)) << PAGE_BITS);
  }
  gpu_part = 0;
  gpu_copy(0, ALC_OFF, up);
  gpu_part = 1;
  if (!up) {  // what a leave reads first: the rings' counters, the marks
    gpu_copy(RING_OFF + RING_LEN * LANES, RING_OFF + (RING_LEN + 2) * LANES,
      false);
    if (gpu_state != NULL) {  // for gpu_heap
      u64 m = H[H_TWIN_MAP] * 8 + gpu_lo / GPU_CHUNK * 4;
      u64 n = (gpu_hi - gpu_lo) / GPU_CHUNK;
      gpu_move(m & ~7ull, (m + n * 4 + 7) & ~7ull, false, true);
    }
    gpu_flush(true);
  }
  gpu_rings(up);
  gpu_part = 2;
  gpu_heap(HEAP_OFF + (((u64)a32_load(a32_at(H, H_BUMP)) + 1) << PAGE_BITS),
    up);
  gpu_part = 3;
  for (Cls c = 0; c < NCLS_ALL; c += 1) {
    Bank* b = bank_at(H, c);
    u32   n = b->wr > b->rd ? b->wr : b->rd;
    n = b->top > n ? b->top : n;
    if (n != 0) {
      gpu_copy(b->off, b->off + n + 1, up);
    }
  }
  gpu_part = 0;
  gpu_flush(!up);
}

#define gpu_enter(k) (gpu_key = (k), gpu_sync(true))
#define gpu_leave() gpu_sync(false)

static void gpu_kernel(u32 pass, u32 groups) {
  struct { Corpus mem; u32 pass; } args = { gpu_vram, pass };
  gpu_launch(gpu_pso, groups, 1, CUBE_T, 1, TG_HOLD * 8, &args, sizeof args);
}

static void gpu_pass(u32 f) {
  gpu_copy(0, ALC_OFF, true);
  gpu_flush(false);
  u64 t0 = gpu_stat ? io_tick() : 0;
  gpu_run(f);
  gpu_copy(0, ALC_OFF, false);
  gpu_flush(true);
  gpu_dev_ns += gpu_stat ? io_tick() - t0 : 0;
}

// Window.frame's fill on the device: the image's chunks go up if the host
// dirtied them (they stay dirty, the next turn sends them again), and
// only the pixels come down.
static void gpu_show(Term image, u32 w, u32 h, u32 k, u32* pix) {
  static hipFunction_t pso;
  static void*         buf;
  static u64           cap;
  u64 len = (u64)w * h * 4;
  struct { Corpus mem; Term root; u32 w; u32 h; u32 k; u32* out; } args;
  _Static_assert(sizeof args == 40, "window args");
  if (pso == NULL && hipModuleGetFunction(&pso, gpu_lib, "window_dev")
    != hipSuccess) {
    err_fail("cannot load the window kernel");
  }
  if (len > cap) {
    if (hipFree(buf) != hipSuccess || hipMalloc(&buf, len) != hipSuccess) {
      err_fail("the frame's device buffer failed");
    }
    cap = len;
  }
  gpu_part = 2;
  gpu_heap(HEAP_OFF
    + (((u64)a32_load(a32_at(CORPUS, H_BUMP)) + 1) << PAGE_BITS), 2);
  gpu_part = 0;
  gpu_flush(false);
  args.mem  = gpu_vram;
  args.root = image;
  args.w    = w;
  args.h    = h;
  args.k    = k;
  args.out  = (u32*)buf;
  gpu_launch(pso, (w + 31) / 32, (h + 7) / 8, 32, 8, 0, &args, sizeof args);
  if (hipMemcpy(pix, buf, len, hipMemcpyDeviceToHost) != hipSuccess) {
    err_fail("the frame's device fill failed");
  }
}
