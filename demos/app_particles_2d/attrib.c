// Stage 1 fault attribution for the HIP lane: attrib.sh splices these
// parts (and reach.c's) into the emitted C of a probe build, with hooks in
// gpu_fault, gpu_sync and the bang seam. Nothing here is in the runtime;
// with BEND_GPU_STATS unset only the phase tags run.
//@ tags
// What the host is doing, per thread: 1 heap_alloc_miss, 2 heap_alloc,
// 3 a free-list link, 4 term_drop, 5 ctr_take or span_fade. The signal
// fences keep the tag stores where they are around a faulting access.
#if !DEVICE && BEND_HIP
static __thread u8  at_in[8];
static __thread u64 at_new[8][2];
static __thread u32 at_newk;
static __thread u64 at_lc;
#define AT_F       __atomic_signal_fence(__ATOMIC_SEQ_CST)
#define AT_IN(k)   (AT_F, at_in[k] += 1, AT_F)
#define AT_OUT(k)  (AT_F, at_in[k] -= 1, AT_F)
#define AT_LC(e, c) \
  (at_lc = (u64)((e).alc - &ALC[0][0]) / (3 * ALC_WORDS) * 32 + (c))
#define AT_NEW(h, c) (at_new[at_newk & 7][0] = (h), \
  at_new[at_newk++ & 7][1] = 1ull << (c))
static void at_pop(Env e, Cls cls, Loc got, bool bank);
static void at_pre(u64 c);
static bool at_fault(u64 c, void* addr, u32 how);
static void at_enter(void);
static void at_leave(void);
static void at_reach_walk(Corpus H);
static void at_arg_walk(void);
static void at_walk_print(double f);
static u32  at_reach(u64 c);
static Term at_arg[8];
static u32  at_argn;
#else
#define AT_IN(k)           ((void)0)
#define AT_OUT(k)          ((void)0)
#define AT_LC(e, c)        ((void)0)
#define AT_NEW(h, c)       ((void)0)
#define at_pop(e, c, g, b) ((void)0)
#endif
//@ host
#if BEND_HIP
// Kinds: what the host was doing at the fault. INIT: a plain write into
// one of the thread's last eight allocations. A kind's name ends in "@"
// when its allocator chain came off a bank from the device.
enum { K_OTHER, K_INIT, K_FREE, K_ALLOC, K_ALLOCD, K_MISS, K_MISSD, K_TAKE,
  K_DROP, K_N };
static const char* at_name[K_N] = { "other", "init", "free", "alloc",
  "alloc@", "miss", "miss@", "take", "drop" };
static u8*   at_cur;       // at the enter: 0 stale, 1 current, 2 past the bump
static u8*   at_dtag;      // 1 + the kind that downloaded the chunk
static u32*  at_mark[5];   // reach (reach.c)
static u8    at_chain[CUBE_T + 1][NCLS_ALL];
static u64   at_nch, at_mw, at_bump, at_bangs, at_frames;
static char* at_buf;         // the host's pre-image, then the device's
static char* at_dev;         // the device's heap as the turn began
static u64   at_devn;        // its chunks
static bool  at_cmp, at_dcmp;
static u64   at_n[2][K_N][3][6];  // [after sim, raster][kind][how][reach]
static u64   at_mat[K_N][K_N];    // downloaded by, first written by
static u64   at_cur_n[3];         // downloads by at_cur
static u64   at_diff[3][6][3];    // [vs host][at_cur], [vs device][reach],
                                  // [vs host][reach]:
                                  // chunks, lines, bytes changed
static u64   at_pops[4];          // bank pops: all, the device's, past the bump
static u64   at_walk[2][8];
static u64   at_hits, at_over;
static u64*  at_set;              // heads the device handed, open addressing
static u64   at_setc;             // (a power of two)
static u32   at_lock;
static u64*  at_snap[NCLS_ALL];
static u32   at_snapn[NCLS_ALL];
#define AT_ADD(p, v) __atomic_fetch_add(&(p), v, __ATOMIC_RELAXED)

static u64* at_slot(u64* set, u64 n, u64 v) {
  u64 i = (v * 0x9E3779B97F4A7C15ull) & (n - 1);
  while (set[i] != 0 && set[i] != v) {
    i = (i + 1) & (n - 1);
  }
  return &set[i];
}

static void at_pop(Env e, Cls cls, Loc got, bool bank) {
  u64 lane = (u64)(e.alc - &ALC[0][0]) / (3 * ALC_WORDS);
  if (!gpu_stat || at_bangs == 0) {
    return;
  }
  at_chain[lane][cls] = 0;
  if (!bank || got == 0) {
    return;
  }
  LOCK(at_lock);
  u64* s   = at_setc ? at_slot(at_set, at_setc, got) : NULL;
  bool dev = s != NULL && *s == got;
  if (dev) {
    *s = 1;  // a tombstone: never a heap Loc
  }
  UNLOCK(at_lock);
  at_chain[lane][cls] = dev || got >= at_bump;
  AT_ADD(at_pops[0], 1);
  AT_ADD(at_pops[1], dev);
  AT_ADD(at_pops[2], got >= at_bump);
}

static u32 at_kind(u64 w) {
  bool d = at_chain[at_lc >> 5][at_lc & 31];
  if (at_in[4]) {
    return K_DROP;
  }
  if (at_in[5]) {
    return K_TAKE;
  }
  if (at_in[1]) {
    return d ? K_MISSD : K_MISS;
  }
  if (at_in[2]) {
    return d ? K_ALLOCD : K_ALLOC;
  }
  if (at_in[3]) {
    return K_FREE;
  }
  for (u32 i = 0; i < 8; i += 1) {
    if (w - at_new[i][0] < at_new[i][1]) {
      return K_INIT;
    }
  }
  return K_OTHER;
}

// Under the fault lock, before the download: the host's last copy (its
// bytes as they were when it last had the chunk) and the device's bytes as
// the turn began
static void at_pre(u64 c) {
  at_cmp = at_cur != NULL && c < at_nch;
  if (at_cmp) {
    memcpy(at_buf, gpu_alias + gpu_lo + c * GPU_CHUNK, GPU_CHUNK);
  }
  at_dcmp = c < at_devn && hipMemcpy(at_buf + GPU_CHUNK, at_dev + c
    * GPU_CHUNK, GPU_CHUNK, hipMemcpyDeviceToHost) == hipSuccess;
}

static void at_diff_add(u64* d, const u8* a, const u8* b) {
  d[0] += 1;
  for (u64 o = 0; o < GPU_CHUNK; o += 128) {
    if (memcmp(a + o, b + o, 128) != 0) {
      d[1] += 1;
      for (u32 j = 0; j < 128; j += 1) {
        d[2] += a[o + j] != b[o + j];
      }
    }
  }
}

// how: 0 a download by a read, 1 by a write, 2 the first write to a
// clean chunk. A download's runs under the lock, after the copy into the
// alias and before the chunk opens, so the bytes it compares are the
// device's alone and its tags are set before another thread can fault.
static bool at_fault(u64 c, void* addr, u32 how) {
  if (at_cur == NULL || c >= at_nch) {
    return true;
  }
  u32 k  = at_kind((u64)((char*)addr - (char*)CORPUS) / 8);
  u32 r  = at_reach(c);
  u32 ph = (at_bangs + 1) & 1;
  AT_ADD(at_n[ph][k][how][r], 1);
  if (how < 2) {
    at_dtag[c] = (u8)(k + 1);
  }
  if (how > 0 && at_dtag[c] != 0) {
    AT_ADD(at_mat[at_dtag[c] - 1][k], 1);
  }
  if (how == 2) {
    return true;
  }
  const u8* now = (const u8*)gpu_alias + gpu_lo + c * GPU_CHUNK;
  at_cur_n[at_cur[c]] += 1;
  if (at_cmp) {
    at_diff_add(at_diff[0][at_cur[c]], (const u8*)at_buf, now);
    at_diff_add(at_diff[2][r], (const u8*)at_buf, now);
  }
  if (at_dcmp) {
    at_diff_add(at_diff[1][r], (const u8*)at_buf + GPU_CHUNK, now);
  }
  wr_fault(c, how, r);
  return true;
}

static void at_print(void) {
  double f = at_frames ? (double)at_frames : 1;
  static const char* how[3] = { "down by read", "down by write",
    "first write" };
  fprintf(stderr, "attrib: %llu frames; per frame; reach: the last result,"
    " through sealed cells, the one before; the last bang's arguments, the"
    " one before's; none\n",
    (unsigned long long)at_frames);
  for (u32 ph = 0; ph < 2; ph += 1) {
    for (u32 k = 0; k < K_N; k += 1) {
      for (u32 h = 0; h < 3; h += 1) {
        u64* n = at_n[ph][k][h];
        if (n[0] + n[1] + n[2] + n[3] + n[4] + n[5] != 0) {
          fprintf(stderr, "attrib: after %s  %-7s %-13s %6.1f %6.1f %6.1f"
            " %6.1f %6.1f %6.1f\n", ph ? "raster" : "sim   ", at_name[k],
            how[h], n[0] / f, n[1] / f, n[2] / f, n[3] / f, n[4] / f,
            n[5] / f);
        }
      }
    }
  }
  for (u32 a = 0; a < K_N; a += 1) {
    for (u32 b = 0; b < K_N; b += 1) {
      if (at_mat[a][b] != 0) {
        fprintf(stderr, "attrib: downloaded by %-7s first written by %-7s"
          " %8.1f\n", at_name[a], at_name[b], at_mat[a][b] / f);
      }
    }
  }
  fprintf(stderr, "attrib: downloads %.1f: stale at the enter %.1f, current"
    " %.1f, past its bump %.1f\n", (at_cur_n[0] + at_cur_n[1] + at_cur_n[2])
    / f, at_cur_n[0] / f, at_cur_n[1] / f, at_cur_n[2] / f);
  for (u32 x = 0; x < 3; x += 1) {
    for (u32 r = 0; r < 6; r += 1) {
      u64* d = at_diff[x][r];
      if (d[0] != 0) {
        fprintf(stderr, "attrib: vs the %s %u: %.1f chunks, %.1f%% of"
          " lines, %.2f%% of bytes changed\n", x == 1
          ? "device's pre-turn, reach" : x ? "host's last copy, reach"
          : "host's last copy, at_cur", r, d[0] / f,
          100.0 * d[1] / (d[0] * 2048.0),
          100.0 * d[2] / (d[0] * (double)GPU_CHUNK));
      }
    }
  }
  fprintf(stderr, "attrib: bank pops %.1f, from the device %.1f, past the"
    " enter's bump %.1f\n", at_pops[0] / f, at_pops[1] / f, at_pops[2] / f);
  at_walk_print(f);
}

static void at_enter(void) {
  Corpus H = CORPUS;
  if (at_cur == NULL) {
    at_nch     = (gpu_hi - gpu_lo) / GPU_CHUNK + 1;
    at_mw      = at_nch / 32 + 1;
    at_cur     = calloc(at_nch, 1);
    at_dtag    = calloc(at_nch, 1);
    for (u32 i = 0; i < 5; i += 1) {
      at_mark[i] = calloc(at_mw, 4);
    }
    at_buf     = malloc(2 * GPU_CHUNK);
    if (hipMalloc((void**)&at_dev, gpu_hi - gpu_lo) != hipSuccess) {
      err_fail("attrib: no room for the heap's snapshot");
    }
    atexit(at_print);
  }
  u64 bump = a32_load(a32_at(H, H_BUMP));
  u64 e    = (HEAP_OFF + ((bump + 1) << PAGE_BITS)) * 8;
  u64 te   = e < gpu_lo ? gpu_lo : e > gpu_hi ? gpu_hi
    : (e + GPU_CHUNK - 1) & ~(GPU_CHUNK - 1);
  u64 n    = (te - gpu_lo) / GPU_CHUNK;
  for (u64 c = 0; c < at_nch; c += 1) {
    at_cur[c]  = c >= n ? 2 : gpu_state[c] != GPU_STALE;
    at_dtag[c] = 0;
  }
  at_bump = HEAP_OFF + (bump << PAGE_BITS);
  at_devn = n;
  hipMemcpy(at_dev, (char*)gpu_vram + gpu_lo, n * GPU_CHUNK,
    hipMemcpyDeviceToDevice);
  at_arg_walk();
  wr_enter(n);
  for (Cls c = 0; c < NCLS_ALL; c += 1) {
    Bank* b = bank_at(H, c);
    at_snap[c]  = realloc(at_snap[c], (b->rd + 1) * 8ull);
    at_snapn[c] = b->rd;
    memcpy(at_snap[c], H + b->off, b->rd * 8ull);
  }
}

// After a turn, before root_take: the banks' heads the device pushed (past
// the longest prefix still as the enter left it), and those an earlier
// turn pushed that are still in that prefix, then the result's reach
static void at_leave(void) {
  Corpus H = CORPUS;
  if (!gpu_stat || at_cur == NULL || a32_load(a32_at(H, H_ROOT_DONE)) == 0) {
    return;
  }
  at_bangs += 1;
  at_frames = at_bangs / 2;
  u64 all = 0;
  for (Cls c = 0; c < NCLS_ALL; c += 1) {
    all += bank_at(H, c)->rd;
  }
  u64* old = at_set;
  u64  oc  = at_setc;
  for (at_setc = 16; at_setc < 2 * all; at_setc *= 2) {
  }
  at_set = calloc(at_setc, 8);
  for (Cls c = 0; c < NCLS_ALL; c += 1) {
    Bank* b = bank_at(H, c);
    u32   i = 0;
    while (i < b->rd && i < at_snapn[c] && H[b->off + i] == at_snap[c][i]) {
      i += 1;
    }
    for (u32 j = 0; j < b->rd; j += 1) {
      u64 v = H[b->off + j];
      if (j >= i || (oc && *at_slot(old, oc, v) == v)) {
        *at_slot(at_set, at_setc, v) = v;
      }
    }
  }
  free(old);
  at_reach_walk(H);
  wr_leave();
}
#endif
