// The device's record of a turn (attrib.sh, writes.c): the slots its
// allocator hands out and where they came from, the free-list links it
// writes, and wdiff_dev, which sorts each changed word by them.
//@ wtags
#define AT_CS 16  // wdiff_dev's counts a chunk
#if DEVICE && defined(__HIPCC_RTC__)
// a bit a tracked word, from word at_w0: the slots the device took this
// turn (at_wa), the free-list links it wrote (at_wf), the slots of the
// chains its bank pops handed (at_wb); of at_wa, a slot below the enter's
// bump off such a chain (at_wsb: adopted), else one the device freed this
// turn (at_wsl: its own), else one a lane held from a turn before (at_wsk:
// carried). NULL: off. Heap reads stay below word at_w0 + at_wlim.
__device__ u32* at_wa;
__device__ u32* at_wf;
__device__ u32* at_wb;
__device__ u32* at_wsb;
__device__ u32* at_wsl;
__device__ u32* at_wsk;
__device__ u64  at_w0, at_wn, at_wlim, at_wbump;

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

__device__ INLINE void at_wnew(u64 h, u64 n) {
  u64 a = h - at_w0;
  if (!at_wa || a >= at_wn) {
    return;
  }
  at_wset(at_wa, h, n);
  if (h < at_wbump) {
    bool bank = at_wb && (at_wb[a >> 5] >> (a & 31) & 1);
    bool own  = at_wf && (at_wf[a >> 5] >> (a & 31) & 1);
    at_wset(bank ? at_wsb : own ? at_wsl : at_wsk, h, n);
  }
}

// a bank pop's chain: at most n slots
__device__ INLINE void at_wbank(Corpus H, u64 got, u32 n) {
  for (u32 i = 0; at_wb && i < n && got != 0; i += 1) {
    u64 a = got - at_w0;
    if (a >= at_wlim) {
      return;
    }
    atomicOr(at_wb + (a >> 5), 1u << (a & 31));
    got = H[got];
  }
}
#undef AT_NEW
#undef at_pop
#define AT_NEW(h, c)       at_wnew(h, 1ull << (c))
#define AT_LINK(l)         at_wset(at_wf, l, 1)
#define at_pop(e, c, g, b) at_wbank((e).mem, g, KEEP(c))
#else
#define AT_LINK(l) ((void)0)
#endif
//@ wkernel
#ifdef BEND_RTC
// a lane a line: the words changed against the enter's image, into
// cs[chunk * AT_CS]: 0 lines, 1 bytes; words 2 the turn took (A), 3 links
// it wrote (F), 4 the turn before took (P), 5 other (L), 6 L with only the
// low 24 bits changed; 7 lines with an L; of A, 8 adopted, 9 own, 10
// carried
extern "C" __global__ void wdiff_dev(const u64* cur, const u64* old,
  const u32* wa, const u32* wp, const u32* wf, const u32* wsb,
  const u32* wsl, const u32* wsk, u32* cs, u64 base, u64 n) {
  u64 i = base + blockIdx.x * (u64)blockDim.x + threadIdx.x;
  if (i >= n) {
    return;
  }
  u32 k[11] = { 0 };
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
    // a slot taken twice may have two sources: the first of these
    u32 o = j != 2 ? 0 : wsb[b] & m ? 8 : wsl[b] & m ? 9 : wsk[b] & m ? 10 : 0;
    k[o] += o != 0;
  }
  k[0] = k[1] != 0;
  k[7] = k[5] != 0;
  for (u32 j = 0; j < 11; j += 1) {
    if (k[j] != 0) {
      atomicAdd(cs + (i >> 11) * AT_CS + j, k[j]);
    }
  }
}
#endif
