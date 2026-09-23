// attrib.sh's printed tallies, per frame.
//@ tally
#if BEND_HIP
static void at_walk_print(double f) {
  static const char* what[4] = { "result", "result through sealed cells",
    "argument words as it began", "argument word " };
  for (u32 p = 0; p < 2; p += 1) {
    for (u32 x = 0; x < 11; x += 1) {
      u64* w = x < 3 ? at_walk[p] + 2 * x : at_warg[p][x - 3];
      if (x < 3 || w[0] != 0) {
        fprintf(stderr, "attrib: %s bang's %s%.1s reach %.0f words in %.1f"
          " chunks\n", p ? "raster" : "sim", what[x < 3 ? x : 3],
          x < 3 ? "" : &"01234567"[x - 3], w[0] / f, w[1] / f);
      }
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
    reach_budget(4096) + RC_SLACK,
    (unsigned long long)at_wfail, at_wfail ? ": MARKS NOT VALID" : "");
}
#endif
