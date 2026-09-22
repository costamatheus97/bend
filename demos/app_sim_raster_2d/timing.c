// Microsecond clock for the sim/raster probe. io_tick is monotonic ns.
Term clock_us_run(Env e, Term* f, IoWork* w) {
  return (Term)(io_tick() / 1000ull);
}

static void __attribute__((constructor)) clock_us_use(void) {
  io_eff(CID_CLOCK_US, clock_us_run, 0);
}
