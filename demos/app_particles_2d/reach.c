// The result's reach for attrib.sh (Stage 1, mark only; Stage 2 would
// prefetch the marked chunks): reach_dev, a device walk next to window_dev,
// and at_reach_walk, its host rounds after each turn. It reads the device's
// copy only, so it moves no chunk and adds no fault.
//@ kernel
// A round walks each queued word depth first like term_drop (a CTR's
// fields, a CLO's captures, an ARR's cells) and marks the 256 KB chunks it
// meets. It stops at leaves and tasks; strict (follow 0), also at sealed
// cells and the bang's argument words; full (follow 1) goes through a
// sealed cell once (seen) to what it holds. A lane past its budget or its
// stack sends the rest to the next round. A node past lim is not read: it
// counts as bad (cnt[3]; the first in cnt[6..7]).
#ifdef BEND_RTC
INLINE void reach_put(Term* q, u32* cnt, u32 cap, Term t) {
  u32 k = atomicAdd(cnt, 1u);
  if (k < cap) {
    q[cap + k] = t;
  } else {
    atomicOr(cnt + 1, 1u);
  }
}

extern "C" __global__ void reach_dev(Corpus H, Term* q, u32* cnt, u32* mark,
  u32* seen, u64 lo, u64 hi, u64 lim, Term a0, Term a1, Term a2, Term a3,
  u32 nin, u32 cap, u32 budget, u32 follow) {
  u32 i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i >= nin) {
    return;
  }
  Term st[48];
  u32  sp    = 0;
  u32  steps = 0;
  u64  words = 0;
  st[sp++] = q[i];
  while (sp > 0) {
    Term t = st[--sp];
    if (term_triv(t)) {
      continue;
    }
    if (!follow && (t == a0 || t == a1 || t == a2 || t == a3)) {
      atomicAdd(cnt + 2, 1u);
      continue;
    }
    if (steps++ >= budget) {
      reach_put(q, cnt, cap, t);
      continue;
    }
    for (u32 z = 0; z < 2; z += 1) {
      u64  tag  = term_tag(t);
      u32  aux  = (u32)term_aux(t);
      Loc  l    = term_loc(t);
      u32  n    = 1;
      bool kids = false;
      bool rfc  = term_rfc(t);
      if (rfc) {
      } else if (tag == TAG_TSK) {
        n = fid_arity(aux) + 2;
      } else if (tag == TAG_BUF) {
        n = 1u << blk_span(t);
      } else {
        kids = true;
        n = tag == TAG_ARR ? 1u << blk_cls(t) : tag == TAG_CTR
          ? cid_arity(aux) : fid_arity(aux) - 1;
      }
      if (l + (n ? n : 1) > lim) {
        atomicAdd(cnt + 3, 1u);
        atomicCAS((unsigned long long*)(cnt + 6), 0ull, t);
        break;
      }
      u64 b0 = l * 8;
      u64 b1 = (l + (n ? n : 1)) * 8 - 1;
      for (u64 c = (b0 - lo) >> 18; b0 >= lo && b1 < hi
        && c <= (b1 - lo) >> 18; c += 1) {
        atomicOr(mark + (c >> 5), 1u << (c & 31));
      }
      words += n;
      for (u32 j = n; kids && j-- > 0;) {
        Term c = H[l + j];
        if (term_triv(c)) {
        } else if (sp < 48) {
          st[sp++] = c;
        } else {
          reach_put(q, cnt, cap, c);
        }
      }
      u64 s = l - HEAP_OFF;
      if (!rfc || !follow || l < HEAP_OFF
        || (atomicOr(seen + (s >> 5), 1u << (s & 31)) >> (s & 31) & 1)) {
        break;
      }
      t = (t & ~(RFC_BIT | LOC_MASK)) | (H[l] >> 24);
      if (term_triv(t)) {
        break;
      }
    }
  }
  atomicAdd((unsigned long long*)(cnt + 4), (unsigned long long)words);
}
#endif
//@ walk
#if BEND_HIP
// at_mark: the last bang's result, strict [0] and full [1], the full reach
// of the one before [2]; the full reach of the last bang's argument words
// as it began [3] and of the one before's [4]. at_walk per bang parity:
// words and chunks of each of the three walks, us, rounds.
static u64 at_bad, at_badt;

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

// w: words and chunks; t: us and rounds
static void at_walk1(const Term* roots, u32 n, u32 follow, u32 to, u64* w,
  u64* t) {
  static hipFunction_t pso;
  static Term*         q;
  static u32*          cnt;
  static u32*          mark;
  static u32*          seen;
  const u32            cap = 1u << 22;
  u64 lim = HEAP_OFF + ((u64)a32_load(a32_at(CORPUS, H_CAP)) << PAGE_BITS);
  u64 sn  = (lim - HEAP_OFF) / 32 * 4 + 4;
  u64 t0  = io_tick();
  u64 all = 0;
  u32 got[8];
  if (pso == NULL && (hipModuleGetFunction(&pso, gpu_lib, "reach_dev")
    != hipSuccess || hipMalloc((void**)&q, 2ull * cap * 8) != hipSuccess
    || hipMalloc((void**)&cnt, 32) != hipSuccess
    || hipMalloc((void**)&mark, at_mw * 4) != hipSuccess
    || hipMalloc((void**)&seen, sn) != hipSuccess)) {
    err_fail("attrib: the reach walker failed");
  }
  hipMemset(mark, 0, at_mw * 4);
  hipMemset(seen, 0, sn);
  hipMemcpy(q, roots, n * 8ull, hipMemcpyHostToDevice);
  for (u32 nin = n, r = 0; nin != 0; t[1] += 1, r += 1) {
    struct { Corpus H; Term* q; u32* cnt; u32* mark; u32* seen; u64 lo;
      u64 hi; u64 lim; Term a[4]; u32 nin; u32 cap; u32 budget; u32 follow; }
      args = { gpu_vram, q, cnt, mark, seen, gpu_lo, gpu_hi, lim, { at_arg[0],
      at_arg[1], at_arg[2], at_arg[3] }, nin, cap, nin < 4096 ? 64 : 4096,
      follow };
    if (r >= (1u << 16) || all > 4 * lim) {
      at_over += 1;  // a cycle or a runaway: stop, the marks are partial
      break;
    }
    size_t len   = sizeof args;
    void*  cfg[] = { HIP_LAUNCH_PARAM_BUFFER_POINTER, &args,
      HIP_LAUNCH_PARAM_BUFFER_SIZE, &len, HIP_LAUNCH_PARAM_END };
    if (hipMemset(cnt, 0, 32) != hipSuccess
      || hipModuleLaunchKernel(pso, (nin + 255) / 256, 1, 1, 256, 1, 1, 0,
        NULL, NULL, cfg) != hipSuccess
      || hipMemcpy(got, cnt, 32, hipMemcpyDeviceToHost) != hipSuccess) {
      err_fail("attrib: the reach walker failed");
    }
    nin      = got[0] < cap ? got[0] : cap;
    if (getenv("ATTRIB_TRACE") != NULL) {
      fprintf(stderr, "walk %u: out %u words %u bad %u\n", follow, got[0],
        got[4], got[3]);
    }
    at_over += got[1];
    at_hits += got[2];
    all     += got[4] | (u64)got[5] << 32;
    w[0]    += got[4] | (u64)got[5] << 32;
    at_bad  += got[3];
    if (at_badt == 0) {
      at_badt = got[6] | (u64)got[7] << 32;
    }
    hipMemcpy(q, q + cap, nin * 8ull, hipMemcpyDeviceToDevice);
  }
  hipMemcpy(at_mark[to], mark, at_mw * 4, hipMemcpyDeviceToHost);
  for (u64 i = 0; i < at_mw; i += 1) {
    w[1] += __builtin_popcount(at_mark[to][i]);
  }
  t[0] += (io_tick() - t0) / 1000;
}

static bool at_walks(void) {
  const char* walk = getenv("BEND_GPU_WALK");
  return walk == NULL || strcmp(walk, "0") != 0;
}

// after the enter's upload: the argument words' reach, before the turn
// frees or reuses any of it
static void at_arg_walk(void) {
  at_rot(3, 4);
  if (at_walks()) {
    at_walk1(at_arg, 4, 1, 3, at_walk[at_bangs & 1] + 4,
      at_walk[at_bangs & 1] + 6);
  }
}

// after the leave, before root_take: the result's
static void at_reach_walk(Corpus H) {
  u32  n = a32_load(a32_at(H, H_ROOT_DONE)) - 1;
  u64* w = at_walk[(at_bangs + 1) & 1];
  at_rot(1, 2);
  if (at_walks()) {
    at_walk1(H + H_ROOT_WORD, n, 0, 0, w, w + 6);
    at_walk1(H + H_ROOT_WORD, n, 1, 1, w + 2, w + 6);
  }
}

static void at_walk_print(double f) {
  static const char* what[3] = { "result", "result through sealed cells",
    "argument words as it began" };
  for (u32 p = 0; p < 2; p += 1) {
    for (u32 x = 0; x < 3; x += 1) {
      u64* w = at_walk[p] + 2 * x;
      fprintf(stderr, "attrib: %s bang's %s reach %.0f words in %.1f"
        " chunks\n", p ? "raster" : "sim", what[x], w[0] / f, w[1] / f);
    }
    fprintf(stderr, "attrib: %s walks %.0f us, %.1f rounds\n",
      p ? "raster" : "sim", at_walk[p][6] / f, at_walk[p][7] / f);
  }
  fprintf(stderr, "attrib: argument words met %llu, walks cut short %llu,"
    " bad words %llu (first %llx)\n", (unsigned long long)at_hits,
    (unsigned long long)at_over, (unsigned long long)at_bad,
    (unsigned long long)at_badt);
}
#endif
