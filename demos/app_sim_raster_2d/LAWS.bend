# Workload profiles, input and the spatial pixel checksum; no F32 claim.
import Base
import ./main.bend as App

law supported_profiles:
  {(App.Scale.parts(16384), App.Scale.parts(65536), App.Scale.parts(262144))
    == (App.Config.small(), App.Config.medium(), App.Config.large()) : Nat & Nat & Nat}

law zero_scale_defaults:
  {App.Scale.parts(0) == App.Config.medium() : Nat}

law esc_stops:
  for rest: List<Event>
  {App.Play.events(Key{27, True{}} <> rest) == False{} : Bool}

# Unlike a sum, the checksum distinguishes these equal-sum pixel permutations.
law pixel_positions:
  {U32.is_eq(App.Image.checksum(1n, Qua{Pix{1}, Pix{2}, Pix{3}, Pix{4}}),
    App.Image.checksum(1n, Qua{Pix{2}, Pix{1}, Pix{3}, Pix{4}})) == False{} : Bool}

law pixel_compression:
  for +color: U32
  {App.Image.checksum(1n, Pix{color})
    == App.Image.checksum(1n, Qua{Pix{color}, Pix{color}, Pix{color}, Pix{color}}) : U32}
