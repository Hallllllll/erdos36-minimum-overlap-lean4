import Overlap.Data

namespace Overlap.Benchmark
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 20000

theorem fullProduct :
    heights.pack (2^128) * heights.other (2^128) 52428700000000 = events.pack (2^128) := by
  decide +kernel
#print axioms fullProduct
end Overlap.Benchmark
