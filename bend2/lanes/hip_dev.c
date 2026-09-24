#if BEND_TWIN
// the enter's mend on the twin (see ring_mend): a thread a ring, from[r]
// its put at the leave
extern "C" __global__ void ring_mend_dev(Corpus H, const u32* from) {
  Ring r = blockIdx.x * blockDim.x + threadIdx.x;
  if (r < LANES) {
    ring_mend(H, r, from[r]);
  }
}

// a flush's pieces (see gpu_stage), 3 words each: the twin's word, the
// host side's address as the device sees it (bit 63: up), the words; a
// group a piece
extern "C" __global__ void gpu_move_dev(Corpus H, const u64* tab, u32 n) {
  for (u32 i = blockIdx.x; i < n; i += gridDim.x) {
    u64* x  = (u64*)(tab[3 * i + 1] & ~(1ull << 63));
    u64  v  = tab[3 * i];
    bool up = tab[3 * i + 1] >> 63;
    for (u64 j = threadIdx.x; j < tab[3 * i + 2]; j += blockDim.x) {
      if (up) {
        H[v + j] = x[j];
      } else {
        x[j] = H[v + j];
      }
    }
  }
}
#endif
