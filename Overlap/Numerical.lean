import Overlap.Data

namespace Overlap
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000

abbrev N : Nat := 9408
abbrev D : Nat := 52428700000000
abbrev B : Nat := 2^128
abbrev peak : Nat := 4924547239055589158644844810158

theorem height_count : heights.size = N := by decide +kernel
theorem height_box : heights.high ≤ D := by decide +kernel
theorem height_mass : 2 * heights.total = N * D := by decide +kernel
theorem event_count : events.size = 2*N-1 := by decide +kernel
theorem event_peak : events.high = peak := by decide +kernel
theorem packed_certificate : heights.pack B * heights.other B D = events.pack B := by decide +kernel
theorem peak_digit : events.items[7123]? = some peak := by decide +kernel
#print axioms packed_certificate
end Overlap
