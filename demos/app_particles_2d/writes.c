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
static void wr_drain(bool enter);
static void wr_zero(void);
static void wr_exit(void);
static u32* at_ab;   // this turn's at_wa, for the result's walk; at_met
static u32* at_met;  // the A words it met, at_amark their chunks
static u32* at_amark;
static u64  at_rA, at_rAd;  // the words it met with their bit set; distinct
static u64  at_tw[2][3];    // us: result strict, full; borrowed argument
static void at_rot(u32 a, u32 b);
#endif
//@ whost
#if BEND_HIP
// Per chunk: at_wacc, what the device wrote since the host's copy was
// current (1 the sim turn, 2 the raster turn, 4 an L word, 8 a P word, 16
// past the enter's image: unknown, 32 an F word); at_wsrc, its A words'
// slots (1 adopted, 2 own, 4 at or past the bump, 8 carried); at_pf, what a
// prefetch at the last leave (at_pfph) would take (1 the result's reach,
// 2 the borrowed argument word's of the bang before, as it began, 4 all
// its argument words'); at_wc, the walk-free ones (at_wcph): 1 downloaded
// after the same leave a frame before (at_whist, a bit a leave), 2 dirty
// at the other turn's last enter (at_wup, a bit a turn). Device: at_wd 0,
// 1 at_wa by parity, 2 at_wf, 3 cs, 4 at_wb, 5 at_wsb, 6 at_wsl, 7 at_met,
// 8 at_wsk.
static u8 * at_wacc, *at_wsrc, *at_pf, *at_wc, *at_wup, *at_whist;
static u32  at_pfph, at_wcph;
static u32* at_wd[9];
static u32* at_bmark[2];
static u32* at_cs;
static u32* at_am;  // at_amark here
static u64  at_snapc, at_wbad[3], at_wfail2, at_wun[2][8];
// per turn: chunks, cs 0..10, rA, rAd, its chunks, chunks with A adopted,
// own, past, carried; per leave: chunks by at_pf and at_wacc (0, A F P, L U),
// runs of at_pf & 1, 3, 5, at_wc 1, 2, either: avoided, prefetched,
// unused; ph acc live how pf same; ph at_wsrc, acc & 60
static u64 at_wt[2][19], at_wpf[2][8][3], at_wrun[2][3], at_wfree[2][3][3];
static u64 at_wdl[2][64][2][2][8][2], at_wsd[2][16][2];
static hipDeviceptr_t at_wg[10];
static bool at_won;

static bool wr_set(u32 g, const void* v) {
  return hipMemcpy((void*)at_wg[g], v, 8, hipMemcpyHostToDevice)
    == hipSuccess;
}

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
  static const char* g[10] = { "at_wa", "at_wf", "at_w0", "at_wn", "at_wb",
    "at_wsb", "at_wsl", "at_wlim", "at_wbump", "at_wsk" };
  // the record's buffers and their globals, at_wa last: it turns them on
  static const u32 rb[6] = { 4, 5, 6, 8, 2, 0 }, rg[6] = { 4, 5, 6, 9, 1, 0 };
  u64 bb = at_nch * (GPU_CHUNK / 8) / 8;  // a bitmap's bytes
  u64 cb = at_nch * AT_CS * 4;             // cs's
  u32 p  = at_bangs & 1;
  if (at_wacc == NULL) {
    u8** b[6] = { &at_wacc, &at_wsrc, &at_pf, &at_wc, &at_wup, &at_whist };
    for (u32 i = 0; i < 6; i += 1) {
      *b[i] = calloc(at_nch, 1);
    }
    at_cs       = calloc(at_nch, AT_CS * 4);
    at_am       = calloc(at_mw, 4);
    at_bmark[0] = calloc(at_mw, 4);
    at_bmark[1] = calloc(at_mw, 4);
    at_won      = hipMalloc((void**)&at_amark, at_mw * 4) == hipSuccess;
    for (u32 i = 0; i < 10; i += 1) {
      size_t len;
      at_won = at_won && hipModuleGetGlobal(&at_wg[i], &len, gpu_lib, g[i])
        == hipSuccess && (i > 8 || (hipMalloc((void**)&at_wd[i], i == 3 ? cb
        : bb) == hipSuccess && hipMemset(at_wd[i], 0, i == 3 ? cb : bb)
        == hipSuccess));
    }
    at_met = at_wd[7];
    u64 w[3] = { gpu_lo / 8, bb * 8, (gpu_hi - gpu_lo) / 8 };
    at_won = at_won && wr_set(2, w) && wr_set(3, w + 1) && wr_set(7, w + 2);
    atexit(wr_exit);
  }
  for (u64 c = 0; c < at_nch; c += 1) {
    u32 up = c < n && gpu_state[c] == GPU_DIRTY;  // this enter sent it
    at_wup[c] = (u8)((at_wup[c] & ~(1u << p)) | up << p);
  }
  u32 jb = p ? 0 : 1;  // Frame.show(+cells, old), Sim.run(+w)
  memset(at_bmark[p], 0, at_mw * 4);
  if (at_walks() && jb < at_argn && !term_triv(at_arg[jb])) {
    u64 w[2] = { 0 }, t[2] = { 0 };
    at_walk1(at_arg + jb, 1, 1, at_bmark[p], w, t);
    at_tw[p][2] += t[0];
  }
  // at_dev: the at_nch - 1 below gpu_hi
  at_snapc = n + 256 < at_nch - 1 ? n + 256 : at_nch - 1;
  const char* rec = getenv("ATTRIB_WREC");
  bool        on  = !rec || strcmp(rec, "0");
  at_won = at_won && dok && hipMemcpy(at_dev + n * GPU_CHUNK,
    (char*)gpu_vram + gpu_lo + n * GPU_CHUNK, (at_snapc - n) * GPU_CHUNK,
    hipMemcpyDeviceToDevice) == hipSuccess && hipMemset(at_met, 0, bb)
    == hipSuccess && hipMemset(at_amark, 0, at_mw * 4) == hipSuccess
    && wr_set(8, &at_bump);
  for (u32 i = 0; i < 6; i += 1) {
    u32*  d = at_wd[i < 5 ? rb[i] : p];
    void* v = on ? d : NULL;
    at_won  = at_won && hipMemset(d, 0, bb) == hipSuccess
      && wr_set(rg[i], &v);
  }
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
    "wdiff_dev") == hipSuccess) && hipMemset(at_wd[3], 0, m * AT_CS * 4)
    == hipSuccess;
  // a dispatch 2^20 lines, each waited for
  for (u64 b = 0; ok && b < m * 2048; b += 1u << 20) {
    struct { u64* cur; char* old; u32* wa; u32* wp; u32* wf; u32* wsb;
      u32* wsl; u32* wsk; u32* cs; u64 base; u64 n; } args = { gpu_vram
      + gpu_lo / 8, at_dev, at_wd[tp], at_wd[1 - tp], at_wd[2], at_wd[5],
      at_wd[6], at_wd[8], at_wd[3], b, m * 2048 };
    size_t len   = sizeof args;
    void*  cfg[] = { HIP_LAUNCH_PARAM_BUFFER_POINTER, &args,
      HIP_LAUNCH_PARAM_BUFFER_SIZE, &len, HIP_LAUNCH_PARAM_END };
    ok = hipModuleLaunchKernel(pso, 4096, 1, 1, 256, 1, 1, 0, NULL, NULL,
      cfg) == hipSuccess && hipDeviceSynchronize() == hipSuccess;
  }
  ok = ok && hipMemcpy(at_cs, at_wd[3], m * AT_CS * 4,
    hipMemcpyDeviceToHost) == hipSuccess;
  bool am = at_won && hipMemcpy(at_am, at_amark, at_mw * 4,
    hipMemcpyDeviceToHost) == hipSuccess;
  at_wfail2 += !ok || !am;
  u64* t   = at_wt[tp];
  u32  run = 0;
  memset(at_pf, 0, at_nch);
  memset(at_wc, 0, at_nch);
  for (u64 c = 0; c < n; c += 1) {
    u32* k  = at_cs + c * AT_CS;
    bool kn = ok && c < m;
    bool w  = !kn || k[0];
    t[0] += w;
    for (u32 j = 0; kn && j < 11; j += 1) {
      t[1 + j] += k[j];
    }
    u32 src = kn ? (k[8] ? 1 : 0) | (k[9] ? 2 : 0) | (k[10] ? 8 : 0)
      | (k[2] > k[8] + k[9] + k[10] ? 4 : 0) : 0;
    for (u32 j = 0; j < 4; j += 1) {
      t[15 + j] += src >> j & 1;
    }
    at_wsrc[c] |= (u8)src;
    at_wacc[c] |= (w << tp) | (kn ? 0 : 16) | (kn && k[5] ? 4 : 0)
      | (kn && k[4] ? 8 : 0) | (kn && k[3] ? 32 : 0);
    u32 b = c >> 5;
    u32 s = c & 31;
    at_pf[c] = (at_mark[1][b] >> s & 1) | (at_bmark[1 - tp][b] >> s & 1)
      << 1 | (at_mark[4][b] >> s & 1) << 2;
    u32 a = at_wacc[c];
    at_wpf[tp][at_pf[c]][a & 20 ? 2 : a & 3 ? 1 : 0] += 1;
    // a run starts where the chunk before was not in it
    for (u32 i = 0; i < 3; i += 1) {
      u32 in = (at_pf[c] & (1 | (i ? 1u << i : 0))) != 0;
      at_wrun[tp][i] += in && !(run >> i & 1);
      run = (run & ~(1u << i)) | in << i;
    }
    at_wc[c] = (u8)((at_whist[c] >> tp & 1) | (at_wup[c] >> (1 - tp) & 1)
      << 1);
    for (u32 v = 0; v < 3; v += 1) {
      at_wfree[tp][v][1] += v < 2 ? at_wc[c] >> v & 1 : at_wc[c] != 0;
    }
  }
  for (u64 c = 0; c < at_nch; c += 1) {
    at_whist[c] &= (u8)~(1u << tp);
  }
  for (u64 i = 0; am && i < at_mw; i += 1) {
    t[14] += __builtin_popcount(at_am[i]);
  }
  at_pfph = at_wcph = tp;
  t[12] += at_rA;
  t[13] += at_rAd;
  at_rA  = at_rAd = 0;
  at_ab  = NULL;
}

// a download, under the lock, before the chunk opens (at_fault)
static void wr_fault(u64 c, u32 how, u32 r) {
  if (at_wacc == NULL) {
    return;
  }
  u32  ph = (at_bangs + 1) & 1;
  u8   a  = at_wacc[c];
  bool hs = at_cmp && memcmp(at_buf, gpu_alias + gpu_lo + c * GPU_CHUNK,
    GPU_CHUNK) == 0;
  at_wbad[at_cur[c]] += !(a & 19) && !hs;
  at_wdl[ph][a & 63][r < 5][how][at_pf[c]][hs] += 1;
  at_wsd[ph][at_wsrc[c] & 15][(a & 60) != 0] += 1;
  for (u32 v = 0; v < 3; v += 1) {
    at_wfree[ph][v][0] += v < 2 ? at_wc[c] >> v & 1 : at_wc[c] != 0;
  }
  at_whist[c] |= (u8)(1u << ph);
  at_pf[c] = 0;
  at_wc[c] = 0;
}
#endif
