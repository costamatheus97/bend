// Native monotonic microseconds for the sim/raster probe. io_tick is the
// runtime's monotonic nanosecond clock; U32 modular subtraction is valid for
// every frame interval (the counter wraps after about 71 minutes).
Term clock_us_run(Env e, Term* f, IoWork* w) {
  return (Term)(uint32_t)(io_tick() / 1000ull);
}

static void __attribute__((constructor)) clock_us_use(void) {
  io_eff(CID_CLOCK_US, clock_us_run, 0);
}
