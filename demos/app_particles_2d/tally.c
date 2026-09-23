// attrib.sh's tallies: per measured frame (after at_warm bangs), the
// last leave's prefetch candidates drained at the exit.
//@ tally
#if BEND_HIP
static void at_print(void) {
  double f = at_frames ? (double)at_frames : 1;
  static const char* how[3] = { "down by read", "down by write",
    "first write" };
  fprintf(stderr, "attrib: %llu frames after the warmups; per frame; reach:"
    " the last result, through sealed cells, the one before; the last bang's"
    " arguments, the one before's; none\n", (unsigned long long)at_frames);
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

// the per-frame counts, at the first measured frame's enter
static void wr_zero(void) {
  memset(at_n, 0, sizeof at_n);
  memset(at_mat, 0, sizeof at_mat);
  memset(at_cur_n, 0, sizeof at_cur_n);
  memset(at_diff, 0, sizeof at_diff);
  memset(at_pops, 0, sizeof at_pops);
  memset(at_walk, 0, sizeof at_walk);
  memset(at_warg, 0, sizeof at_warg);
  memset(at_tw, 0, sizeof at_tw);
  memset(at_wun, 0, sizeof at_wun);
  memset(at_wt, 0, sizeof at_wt);
  memset(at_wpf, 0, sizeof at_wpf);
  memset(at_wrun, 0, sizeof at_wrun);
  memset(at_wdl, 0, sizeof at_wdl);
  memset(at_wsd, 0, sizeof at_wsd);
  memset(at_wfree, 0, sizeof at_wfree);
}

// the last leave's candidates no download took: unused; at an enter, a
// chunk the host has current starts its account again
static void wr_drain(bool enter) {
  for (u64 c = 0; at_wacc != NULL && c < at_nch; c += 1) {
    at_wun[at_pfph][at_pf[c]] += at_pf[c] != 0;
    for (u32 v = 0; v < 3; v += 1) {
      at_wfree[at_wcph][v][2] += v < 2 ? at_wc[c] >> v & 1 : at_wc[c] != 0;
    }
    at_pf[c] = 0;
    at_wc[c] = 0;
    if (enter && at_cur[c]) {
      at_wacc[c] = 0;
      at_wsrc[c] = 0;
    }
  }
}

static void wr_exit(void) {
  static const char* tn[2] = { "sim", "raster" };
  static const char* vn[3] = { "history", "uploads", "either" };
  double f = at_frames ? (double)at_frames : 1;
  wr_drain(false);
  for (u32 p = 0; p < 2; p += 1) {
    u64* t = at_wt[p];
    fprintf(stderr, "attrib: w %s turn wrote %.1f chunks, %.1f lines, %.0f"
      " bytes; words A %.0f F %.0f P %.0f L %.0f (low 24 bits %.0f), lines"
      " with L %.1f; the result met %.0f A words\n", tn[p], t[0] / f,
      t[1] / f, t[2] / f, t[3] / f, t[4] / f, t[5] / f, t[6] / f, t[7] / f,
      t[8] / f, t[12] / f);
    fprintf(stderr, "attrib: w2 %s A words adopted %.0f own %.0f carried"
      " %.0f past the bump %.0f; chunks with them %.1f %.1f %.1f %.1f; the"
      " result met %.0f distinct A words in %.1f chunks; walks us: result"
      " strict %.0f full %.0f, borrowed argument %.0f\n", tn[p], t[9] / f,
      t[10] / f, t[11] / f, (t[3] - t[9] - t[10] - t[11]) / f, t[15] / f,
      t[16] / f, t[18] / f, t[17] / f, t[13] / f, t[14] / f,
      at_tw[p][0] / f, at_tw[p][1] / f, at_tw[p][2] / f);
    for (u32 v = 0; v < 8; v += 1) {
      fprintf(stderr, "attrib: w pf %s %u chunks unwritten %.1f, A F P %.1f,"
        " L %.1f; unused %.1f\n", tn[p], v, at_wpf[p][v][0] / f,
        at_wpf[p][v][1] / f, at_wpf[p][v][2] / f, at_wun[p][v] / f);
    }
    fprintf(stderr, "attrib: w runs %s %.1f %.1f %.1f\n", tn[p],
      at_wrun[p][0] / f, at_wrun[p][1] / f, at_wrun[p][2] / f);
    for (u32 v = 0; v < 3; v += 1) {
      fprintf(stderr, "attrib: w free %s %s avoided %.1f prefetched %.1f"
        " unused %.1f\n", tn[p], vn[v], at_wfree[p][v][0] / f,
        at_wfree[p][v][1] / f, at_wfree[p][v][2] / f);
    }
  }
  fprintf(stderr, "attrib: w gate: device said unwritten, host saw a"
    " change: %llu stale, %llu current, %llu past the bump; failed leaves"
    " %llu\n", (unsigned long long)at_wbad[0], (unsigned long long)at_wbad[1],
    (unsigned long long)at_wbad[2], (unsigned long long)at_wfail2);
  for (u32 i = 0; i < 8192; i += 1) {  // ph acc live how pf same
    u64 x = (&at_wdl[0][0][0][0][0][0])[i];
    if (x != 0) {
      fprintf(stderr, "attrib: wd %u %u %u %u %u %u %.3f\n", i >> 12,
        i >> 6 & 63, i >> 5 & 1, i >> 4 & 1, i >> 1 & 7, i & 1, x / f);
    }
  }
  for (u32 i = 0; i < 64; i += 1) {  // ph src other
    u64 x = (&at_wsd[0][0][0])[i];
    if (x != 0) {
      fprintf(stderr, "attrib: ws %u %u %u %.3f\n", i >> 5, i >> 1 & 15,
        i & 1, x / f);
    }
  }
}
#endif
