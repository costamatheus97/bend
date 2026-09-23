// What each device turn wrote (attrib.sh): at the leave wdiff_dev diffs
// the heap against at_dev, the enter's image, and the device's record of
// the slots it took and the free-list links it wrote names each changed
// word's kind. A download counts by what the device wrote to its chunk
// since the host's copy was current, and what a prefetch would take.
//@ wdecl
#if BEND_HIP
static void wr_enter(u64 n, bool dok);
static void wr_leave(void);
static void wr_fault(u64 c, u32 how, u32 r);
static u32* at_ab;  // this turn's at_wa, for the result's walk
static u64  at_rA;  // the words it met with their bit set
static void at_rot(u32 a, u32 b);
#endif
//@ wtags
#if DEVICE && defined(__HIPCC_RTC__)
// a bit a tracked word, from word at_w0: the slots the device took this
// turn (at_wa) and the free-list links it wrote (at_wf); NULL: off
__device__ u32* at_wa;
__device__ u32* at_wf;
__device__ u64  at_w0, at_wn;

__device__ INLINE void at_wset(u32* m, u64 l, u64 n) {
  u64 a = l - at_w0;
  if (!m || a >= at_wn) {
    return;
  }
  n = n < at_wn - a ? n : at_wn - a;
  for (u64 i = a, e = a + n; i < e;) {
    u32 k = e - i < 32 - (i & 31) ? (u32)(e - i) : 32 - (u32)(i & 31);
    atomicOr(m + (i >> 5), (k == 32 ? ~0u : (1u << k) - 1) << (i & 31));
    i += k;
  }
}
#undef AT_NEW
#define AT_NEW(h, c) at_wset(at_wa, h, 1ull << (c))
#define AT_LINK(l)   at_wset(at_wf, l, 1)
#else
#define AT_LINK(l) ((void)0)
#endif
//@ wkernel
#ifdef BEND_RTC
// a lane a line: the words changed against the enter's image, into
// cs[chunk * 8]: 0 lines, 1 bytes; words 2 the turn took (A), 3 links it
// wrote (F), 4 the turn before took (P), 5 other (L), 6 L with only the
// low 24 bits changed; 7 lines with an L
extern "C" __global__ void wdiff_dev(const u64* cur, const u64* old,
  const u32* wa, const u32* wp, const u32* wf, u32* cs, u64 base, u64 n) {
  u64 i = base + blockIdx.x * (u64)blockDim.x + threadIdx.x;
  if (i >= n) {
    return;
  }
  u32 k[8] = { 0 };
  for (u64 w = i * 16; w < i * 16 + 16; w += 1) {
    u64 x = cur[w] ^ old[w];
    u32 b = (u32)(w >> 5);
    u32 m = 1u << (w & 31);
    for (u32 y = 0; y < 64; y += 8) {
      k[1] += (x >> y & 255) != 0;
    }
    u32 j = x == 0 ? 0 : wa[b] & m ? 2 : wf[b] & m ? 3 : wp[b] & m ? 4 : 5;
    k[j] += j != 0;
    k[6] += j == 5 && x < (1u << 24);
  }
  k[0] = k[1] != 0;
  k[7] = k[5] != 0;
  for (u32 j = 0; j < 8; j += 1) {
    if (k[j] != 0) {
      atomicAdd(cs + (i >> 11) * 8 + j, k[j]);
    }
  }
}
#endif
//@ whost
#if BEND_HIP
// Per chunk: at_wacc, what the device wrote since the host's copy was
// current (1 the sim turn, 2 the raster turn, 4 an L word, 8 a P word, 16
// past the enter's image: unknown); at_pf, what a prefetch at the last
// leave would take (1 the result's reach, 2 the borrowed argument word's
// of the bang before, as it began, 4 all its argument words'). Device:
// at_wd 0, 1 at_wa by parity, 2 at_wf, 3 cs.
static u8*  at_wacc;
static u8*  at_pf;
static u32* at_wd[4];
static u32* at_bmark[2];
static u32* at_cs;
static u64  at_snapc, at_wbad[3], at_wfail2, at_wun[8];
static u64  at_wt[2][10];   // per turn: chunks, cs 0..7, rA
static u64  at_wpf[8][3];   // chunks by at_pf; by at_wacc: 0, only A F P, L U
static u64  at_wrun[3];     // runs of pf & 1, 3, 5
static u64  at_wdl[2][32][2][2][8][2];  // ph, acc, live, how, pf, host same
static hipDeviceptr_t at_wg[4];  // at_wa, at_wf, at_w0, at_wn
static bool at_won;

static bool wr_set(u32 g, const void* v) {
  return hipMemcpy((void*)at_wg[g], v, 8, hipMemcpyHostToDevice)
    == hipSuccess;
}

static void wr_print(void);

static u32 at_reach(u64 c) {
  for (u32 r = 0; r < 5; r += 1) {
    if (at_mark[r][c >> 5] >> (c & 31) & 1) {
      return r;
    }
  }
  return 5;
}

static void at_rot(u32 a, u32 b) {
  u32* m = at_mark[b];
  at_mark[b] = at_mark[a];
  at_mark[a] = m;
}

// at the enter, after at_arg_walk (n: the chunks under the bump, dok:
// their snapshot)
static void wr_enter(u64 n, bool dok) {
  static const char* g[4] = { "at_wa", "at_wf", "at_w0", "at_wn" };
  u64 bb = at_nch * (GPU_CHUNK / 8) / 8;  // a bitmap's bytes
  u32 p  = at_bangs & 1;
  if (at_wacc == NULL) {
    at_wacc     = calloc(at_nch, 1);
    at_pf       = calloc(at_nch, 1);
    at_cs       = calloc(at_nch, 32);
    at_bmark[0] = calloc(at_mw, 4);
    at_bmark[1] = calloc(at_mw, 4);
    at_won      = true;
    for (u32 i = 0; i < 4; i += 1) {
      size_t len;
      at_won = at_won && hipModuleGetGlobal(&at_wg[i], &len, gpu_lib, g[i])
        == hipSuccess && hipMalloc((void**)&at_wd[i], i < 3 ? bb
        : at_nch * 32) == hipSuccess && hipMemset(at_wd[i], 0, i < 3 ? bb
        : at_nch * 32) == hipSuccess;
    }
    u64 w0 = gpu_lo / 8;
    u64 wn = bb * 8;
    at_won = at_won && wr_set(2, &w0) && wr_set(3, &wn);
    atexit(wr_print);
  }
  for (u64 c = 0; c < at_nch; c += 1) {
    for (u32 b = 0; b < 8; b += 1) {
      at_wun[b] += at_pf[c] == b && b != 0;
    }
    at_pf[c]   = 0;
    at_wacc[c] = at_cur[c] ? 0 : at_wacc[c];
  }
  u32 jb = p ? 0 : 1;  // Frame.show(+cells, old), Sim.run(+w)
  memset(at_bmark[p], 0, at_mw * 4);
  if (at_walks() && jb < at_argn && !term_triv(at_arg[jb])) {
    u64 w[2] = { 0 }, t[2] = { 0 };
    at_walk1(at_arg + jb, 1, 1, at_bmark[p], w, t);
  }
  // at_dev: the at_nch - 1 below gpu_hi
  at_snapc = n + 256 < at_nch - 1 ? n + 256 : at_nch - 1;
  const char* rec = getenv("ATTRIB_WREC");
  void*       wa  = rec && !strcmp(rec, "0") ? NULL : at_wd[p];
  void*       wf  = wa ? at_wd[2] : NULL;
  at_won = at_won && dok && hipMemcpy(at_dev + n * GPU_CHUNK,
    (char*)gpu_vram + gpu_lo + n * GPU_CHUNK, (at_snapc - n) * GPU_CHUNK,
    hipMemcpyDeviceToDevice) == hipSuccess && hipMemset(at_wd[p], 0, bb)
    == hipSuccess && hipMemset(at_wd[2], 0, bb) == hipSuccess
    && wr_set(0, &wa) && wr_set(1, &wf);
  at_ab = at_won ? at_wd[p] : NULL;
}

// at the leave, after the result's walk
static void wr_leave(void) {
  static hipFunction_t pso;
  u32 tp   = (at_bangs + 1) & 1;
  u64 bump = a32_load(a32_at(CORPUS, H_BUMP));
  u64 e    = (HEAP_OFF + ((bump + 1) << PAGE_BITS)) * 8;
  u64 te   = e < gpu_lo ? gpu_lo : e > gpu_hi ? gpu_hi
    : (e + GPU_CHUNK - 1) & ~(GPU_CHUNK - 1);
  u64 n    = (te - gpu_lo) / GPU_CHUNK;
  u64 m    = n < at_snapc ? n : at_snapc;
  bool ok  = at_won && (pso != NULL || hipModuleGetFunction(&pso, gpu_lib,
    "wdiff_dev") == hipSuccess) && hipMemset(at_wd[3], 0, m * 32)
    == hipSuccess;
  // a dispatch 2^20 lines, each waited for
  for (u64 b = 0; ok && b < m * 2048; b += 1u << 20) {
    struct { u64* cur; char* old; u32* wa; u32* wp; u32* wf; u32* cs;
      u64 base; u64 n; } args = { gpu_vram + gpu_lo / 8, at_dev,
      at_wd[tp], at_wd[1 - tp], at_wd[2], at_wd[3], b, m * 2048 };
    size_t len   = sizeof args;
    void*  cfg[] = { HIP_LAUNCH_PARAM_BUFFER_POINTER, &args,
      HIP_LAUNCH_PARAM_BUFFER_SIZE, &len, HIP_LAUNCH_PARAM_END };
    ok = hipModuleLaunchKernel(pso, 4096, 1, 1, 256, 1, 1, 0, NULL, NULL,
      cfg) == hipSuccess && hipDeviceSynchronize() == hipSuccess;
  }
  ok = ok && hipMemcpy(at_cs, at_wd[3], m * 32, hipMemcpyDeviceToHost)
    == hipSuccess;
  at_wfail2 += !ok;
  u64* t   = at_wt[tp];
  u32  run = 0;
  for (u64 c = 0; c < n; c += 1) {
    u32* k = at_cs + c * 8;
    bool w = !ok || c >= m || k[0];
    t[0] += w;
    for (u32 j = 0; ok && c < m && j < 8; j += 1) {
      t[1 + j] += k[j];
    }
    bool kn = ok && c < m;
    at_wacc[c] |= (w << tp) | (kn ? 0 : 16) | (kn && k[5] ? 4 : 0)
      | (kn && k[4] ? 8 : 0);
    u32 b = c >> 5;
    u32 s = c & 31;
    at_pf[c] = (at_mark[1][b] >> s & 1) | (at_bmark[1 - tp][b] >> s & 1)
      << 1 | (at_mark[4][b] >> s & 1) << 2;
    u32 a = at_wacc[c];
    at_wpf[at_pf[c]][a & 20 ? 2 : a & 3 ? 1 : 0] += 1;
    // a run starts where the chunk before was not in it
    for (u32 i = 0; i < 3; i += 1) {
      u32 in = (at_pf[c] & (1 | (i ? 1u << i : 0))) != 0;
      at_wrun[i] += in && !(run >> i & 1);
      run = (run & ~(1u << i)) | in << i;
    }
  }
  t[9] += at_rA;
  at_rA = 0;
  at_ab = NULL;
}

// a download, under the lock, before the chunk opens (at_fault)
static void wr_fault(u64 c, u32 how, u32 r) {
  if (at_wacc == NULL) {
    return;
  }
  u8   a  = at_wacc[c];
  bool hs = at_cmp && memcmp(at_buf, gpu_alias + gpu_lo + c * GPU_CHUNK,
    GPU_CHUNK) == 0;
  at_wbad[at_cur[c]] += !(a & 19) && !hs;
  at_wdl[(at_bangs + 1) & 1][a & 31][r < 5][how][at_pf[c]][hs] += 1;
  at_pf[c] = 0;
}

static void wr_print(void) {
  double f = at_frames ? (double)at_frames : 1;
  for (u32 p = 0; p < 2; p += 1) {
    u64* t = at_wt[p];
    fprintf(stderr, "attrib: w %s turn wrote %.1f chunks, %.1f lines, %.0f"
      " bytes; words A %.0f F %.0f P %.0f L %.0f (low 24 bits %.0f), lines"
      " with L %.1f; the result met %.0f A words\n", p ? "raster" : "sim",
      t[0] / f, t[1] / f, t[2] / f, t[3] / f, t[4] / f, t[5] / f, t[6] / f,
      t[7] / f, t[8] / f, t[9] / f);
  }
  for (u32 v = 0; v < 8; v += 1) {
    fprintf(stderr, "attrib: w pf %u chunks unwritten %.1f, A F P %.1f, L"
      " %.1f; unused %.1f\n", v, at_wpf[v][0] / f, at_wpf[v][1] / f,
      at_wpf[v][2] / f, at_wun[v] / f);
  }
  fprintf(stderr, "attrib: w runs %.1f %.1f %.1f; gate: device said"
    " unwritten, host saw a change: %llu stale, %llu current, %llu past the"
    " bump; failed leaves %llu\n", at_wrun[0] / f, at_wrun[1] / f,
    at_wrun[2] / f, (unsigned long long)at_wbad[0],
    (unsigned long long)at_wbad[1], (unsigned long long)at_wbad[2],
    (unsigned long long)at_wfail2);
  // ph acc live how pf same
  for (u32 i = 0; i < 4096; i += 1) {
    u64 x = (&at_wdl[0][0][0][0][0][0])[i];
    if (x != 0) {
      fprintf(stderr, "attrib: wd %u %u %u %u %u %u %.3f\n", i >> 11,
        i >> 6 & 31, i >> 5 & 1, i >> 4 & 1, i >> 1 & 7, i & 1, x / f);
    }
  }
}
#endif
