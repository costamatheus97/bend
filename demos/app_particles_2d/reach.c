// reach_dev, attrib.sh's device walk next to window_dev, and its host
// rounds: the chunks a bang's result and argument words reach. It reads
// the device's copy only: it moves no chunk and adds no fault.
//@ kernel
// A lane walks its queued word depth first like term_drop (a CTR's
// fields, a CLO's captures, an ARR's cells) and marks the 256 KB chunks it
// meets. It stops at leaves and tasks; strict (follow 0), also at sealed
// cells and the bang's argument words; full (follow 1) goes through a
// sealed cell once (seen) to what it holds. So that no dispatch runs long
// enough to reset the driver: a bad tag or table index, or a node past
// lim, is not read (cnt[3]; the first in cnt[6..7]); a block over
// 2^RC_PIECE words goes back as its halves (cnt[9]); a lane steps once a
// word popped or read, and past its budget sends the rest to the next
// round; a dispatch runs at most RC_LANES lanes. The most a lane stepped,
// cnt[8], is under its budget and RC_SLACK: the node that crossed it (a
// sealed cell and what it holds) and a pop a word left on its stack. All
// the lanes' steps: cnt[10..11], for the host's cap on a walk.
#define RC_PIECE 8
#define RC_STACK 48
#define RC_LANES (1u << 15)
#define RC_WORK  (1u << 24)
#define RC_SLACK ((1u << RC_PIECE) + 2 + RC_STACK)
#define RC_ALL   (1ull << 28)  // a walk's steps, checked each dispatch

// a lane's steps in a round of nin: RC_WORK a dispatch; 64 while few,
// so the walk fans out
INLINE u32 reach_budget(u32 nin) {
  u32 b = nin < 4096 ? 64 : RC_WORK / (nin < RC_LANES ? nin : RC_LANES);
  return b < 64 ? 64 : b > (1u << 14) ? 1u << 14 : b;
}

#if defined(BEND_RTC) || defined(REACH_HOST)
#ifndef REACH_DEV
#define REACH_DEV extern "C" __global__ void
#define REACH_ID  (blockIdx.x * blockDim.x + threadIdx.x)
#endif

INLINE void reach_put(Term* q, u32* cnt, u32 cap, Term t) {
  u32 k = atomicAdd(cnt, 1u);
  if (k < cap) {
    q[cap + k] = t;
  } else {
    atomicOr(cnt + 1, 1u);
  }
}

// a node's words, ~0 for a bad tag or table index; kids: to follow
INLINE u64 reach_span(Term t, bool* kids) {
  u64 tag = term_tag(t);
  u32 aux = (u32)term_aux(t);
  *kids = tag == TAG_CTR || tag == TAG_CLO || tag == TAG_ARR;
  if (tag == TAG_CTR) {
    return aux < sizeof CID_ARITY_T ? cid_arity(aux) : ~0ull;
  }
  if (tag == TAG_CLO || tag == TAG_TSK) {
    if (aux >= sizeof FID_ARITY_T || (tag == TAG_CLO && !fid_arity(aux))) {
      return ~0ull;
    }
    return tag == TAG_CLO ? fid_arity(aux) - 1 : fid_arity(aux) + 2;
  }
  return tag == TAG_BUF || tag == TAG_ARR ? 1ull << blk_span(t) : ~0ull;
}

REACH_DEV reach_dev(Corpus H, Term* q, u32* cnt, u32* mark, u32* seen,
  const Term* av, u64 lo, u64 hi, u64 lim, u32 na, u32 base, u32 nin,
  u32 cap, u32 budget, u32 follow) {
  u32 i = base + REACH_ID;
  if (i >= nin) {
    return;
  }
  Term st[RC_STACK];
  u32  sp    = 0;
  u32  steps = 0;
  u64  words = 0;
  st[sp++] = q[i];
  while (sp > 0) {
    Term t   = st[--sp];
    bool arg = false;
    steps += 1;
    if (term_triv(t)) {
      continue;
    }
    for (u32 j = 0; !follow && j < na; j += 1) {
      arg = arg || t == av[j];
    }
    if (arg) {
      atomicAdd(cnt + 2, 1u);
      continue;
    }
    if (steps > budget) {
      reach_put(q, cnt, cap, t);
      continue;
    }
    for (u32 z = 0; z < 2; z += 1) {
      bool kids = false;
      bool rfc  = term_rfc(t);
      u64  n    = rfc ? 1 : reach_span(t, &kids);
      Loc  l    = term_loc(t);
      if (n == ~0ull || l + (n ? n : 1) > lim) {
        atomicAdd(cnt + 3, 1u);
        atomicCAS((unsigned long long*)(cnt + 6), 0ull, t);
        break;
      }
      if (!rfc && n > (1u << RC_PIECE)) {
        Term h = (t & ~(LOC_MASK | (31ull << 40)))
          | (u64)(blk_cls(t) - 1) << 40;
        for (u32 k = 0; k < 2; k += 1) {
          Term p = h | (l + (k ? 0 : n / 2));
          if (sp < RC_STACK) {
            st[sp++] = p;
          } else {
            reach_put(q, cnt, cap, p);
          }
        }
        atomicAdd(cnt + 9, 1u);
        break;
      }
      u64 b0 = l * 8;
      u64 b1 = (l + (n ? n : 1)) * 8 - 1;
      for (u64 c = (b0 - lo) >> 18; b0 >= lo && b1 < hi
        && c <= (b1 - lo) >> 18; c += 1) {
        atomicOr(mark + (c >> 5), 1u << (c & 31));
      }
      words += n;
      steps += (u32)n;
      for (u32 j = (u32)n; kids && j-- > 0;) {
        Term c = H[l + j];
        if (term_triv(c)) {
        } else if (sp < RC_STACK) {
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
  atomicAdd((unsigned long long*)(cnt + 10), (unsigned long long)steps);
  atomicMax(cnt + 8, steps);
}
#endif
//@ walk
#if BEND_HIP
// at_mark: the last bang's result, strict [0] and full [1], the full reach
// of the one before [2]; the full reach of the last bang's argument words
// as it began [3] and of the one before's [4]. at_walk per bang parity:
// words and chunks of the three walks, us, rounds; at_warg per argument
// word, each walked alone.
static u64 at_bad, at_badt, at_wfail, at_step, at_split;
static u64 at_warg[2][8][2];

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

// into out; w: words, chunks; t: us, rounds. A failed HIP call leaves out
// empty and counts in at_wfail.
static void at_walk1(const Term* roots, u32 n, u32 follow, u32* out, u64* w,
  u64* t) {
  static hipFunction_t pso;
  static Term*         q;
  static u32*          cnt;
  static u32*          mark;
  static u32*          seen;
  static Term*         av;
  static u64           slim;
  const u32            cap = 1u << 22;
  u64 lim = HEAP_OFF + ((u64)a32_load(a32_at(CORPUS, H_CAP)) << PAGE_BITS);
  u64 t0  = io_tick();
  u64 all = 0;  // steps
  u64 wds = 0;
  u32 got[16];
  static u32 up;  // 1 ready, 2 failed
  if (up == 0) {
    slim = lim;
    up   = hipModuleGetFunction(&pso, gpu_lib, "reach_dev") == hipSuccess
      && hipMalloc((void**)&q, 2ull * cap * 8) == hipSuccess
      && hipMalloc((void**)&cnt, 64) == hipSuccess
      && hipMalloc((void**)&mark, at_mw * 4) == hipSuccess
      && hipMalloc((void**)&av, 64) == hipSuccess
      && hipMalloc((void**)&seen, (slim - HEAP_OFF) / 8 + 8) == hipSuccess
      ? 1 : 2;
  }
  bool ok = up == 1 && n <= cap;
  lim = lim < slim ? lim : slim;
  ok  = ok && hipMemset(mark, 0, at_mw * 4) == hipSuccess
    && hipMemset(seen, 0, (slim - HEAP_OFF) / 8 + 8) == hipSuccess
    && hipMemcpy(av, at_arg, 64, hipMemcpyHostToDevice) == hipSuccess
    && hipMemcpy(q, roots, n * 8ull, hipMemcpyHostToDevice) == hipSuccess;
  for (u32 nin = n, r = 0; ok && nin != 0; t[1] += 1, r += 1) {
    if (r >= 4096 || all > RC_ALL) {
      at_over += 1;  // a cycle or a runaway: partial marks
      break;
    }
    ok     = hipMemset(cnt, 0, 64) == hipSuccess;
    got[10] = got[11] = 0;
    for (u32 b = 0; ok && b < nin && all + (got[10] | (u64)got[11] << 32)
      <= RC_ALL; b += RC_LANES) {
      struct { Corpus H; Term* q; u32* cnt; u32* mark; u32* seen; Term* av;
        u64 lo; u64 hi; u64 lim; u32 na; u32 base; u32 nin; u32 cap;
        u32 budget; u32 follow; } args = { gpu_vram, q, cnt, mark, seen, av,
        gpu_lo, gpu_hi, lim, at_argn, b, nin, cap, reach_budget(nin),
        follow };
      u32    lanes = nin - b < RC_LANES ? nin - b : RC_LANES;
      size_t len   = sizeof args;
      void*  cfg[] = { HIP_LAUNCH_PARAM_BUFFER_POINTER, &args,
        HIP_LAUNCH_PARAM_BUFFER_SIZE, &len, HIP_LAUNCH_PARAM_END };
      ok = hipModuleLaunchKernel(pso, (lanes + 255) / 256, 1, 1, 256, 1, 1,
        0, NULL, NULL, cfg) == hipSuccess
        && hipMemcpy(got, cnt, 64, hipMemcpyDeviceToHost) == hipSuccess;
    }
    if (!ok) {
      break;
    }
    nin = got[0] < cap ? got[0] : cap;
    at_over  += got[1];
    at_hits  += got[2];
    all      += got[10] | (u64)got[11] << 32;
    wds      += got[4] | (u64)got[5] << 32;
    at_bad   += got[3];
    at_split += got[9];
    at_step   = got[8] > at_step ? got[8] : at_step;
    if (at_badt == 0) {
      at_badt = got[6] | (u64)got[7] << 32;
    }
    ok = hipMemcpy(q, q + cap, nin * 8ull, hipMemcpyDeviceToDevice)
      == hipSuccess;
  }
  ok = ok && hipMemcpy(out, mark, at_mw * 4, hipMemcpyDeviceToHost)
    == hipSuccess;
  if (!ok) {
    at_wfail += 1;
    memset(out, 0, at_mw * 4);
    wds = 0;
  }
  w[0] += wds;
  for (u64 i = 0; i < at_mw; i += 1) {
    w[1] += __builtin_popcount(out[i]);
  }
  t[0] += (io_tick() - t0) / 1000;
}

static bool at_walks(void) {
  const char* w = getenv("BEND_GPU_WALK");
  return !w || strcmp(w, "0");
}

// after the enter's upload, before the turn frees or reuses any of it:
// the argument words' reach, all at once, then each alone
static void at_arg_walk(void) {
  static u32* one;
  u64*        w = at_walk[at_bangs & 1];
  one = one ? one : calloc(at_mw, 4);
  at_rot(3, 4);
  if (at_walks()) {
    at_walk1(at_arg, at_argn, 1, at_mark[3], w + 4, w + 6);
    for (u32 j = 0; j < at_argn; j += 1) {
      if (!term_triv(at_arg[j])) {
        at_walk1(at_arg + j, 1, 1, one, at_warg[at_bangs & 1][j], w + 6);
      }
    }
  }
}

// after the leave, before root_take: the result's
static void at_reach_walk(Corpus H) {
  u32  n = a32_load(a32_at(H, H_ROOT_DONE)) - 1;
  u64* w = at_walk[(at_bangs + 1) & 1];
  at_rot(1, 2);
  if (at_walks()) {
    at_walk1(H + H_ROOT_WORD, n, 0, at_mark[0], w, w + 6);
    at_walk1(H + H_ROOT_WORD, n, 1, at_mark[1], w + 2, w + 6);
  }
}

static void at_walk_print(double f) {
  static const char* what[11] = { "result", "result through sealed cells",
    "argument words as it began", "0", "1", "2", "3", "4", "5", "6", "7" };
  for (u32 p = 0; p < 2; p += 1) {
    for (u32 x = 0; x < 11; x += 1) {
      u64* w = x < 3 ? at_walk[p] + 2 * x : at_warg[p][x - 3];
      if (x >= 3 && w[0] == 0) {
        continue;
      }
      fprintf(stderr, "attrib: %s bang's %s%s reach %.0f words in %.1f"
        " chunks\n", p ? "raster" : "sim", x < 3 ? "" : "argument word ",
        what[x], w[0] / f, w[1] / f);
    }
    fprintf(stderr, "attrib: %s walks %.0f us, %.1f rounds\n",
      p ? "raster" : "sim", at_walk[p][6] / f, at_walk[p][7] / f);
  }
  fprintf(stderr, "attrib: argument words met %llu, walks cut short %llu,"
    " bad words %llu (first %llx), blocks split %llu, most steps a lane"
    " %llu (bound %u), walks failed %llu%s\n",
    (unsigned long long)at_hits, (unsigned long long)at_over,
    (unsigned long long)at_bad, (unsigned long long)at_badt,
    (unsigned long long)at_split, (unsigned long long)at_step,
    (1u << 14) + RC_SLACK,
    (unsigned long long)at_wfail, at_wfail ? ": MARKS NOT VALID" : "");
}
#endif
