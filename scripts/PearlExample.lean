import Overlap.Algebra
import Overlap.AffineBridge

namespace PearlExample
open Overlap

theorem toy_digits : exactDigits [2, 1, 0] 2 = [4, 4, 1, 0, 0] := by decide +kernel

example : Nat.ofDigits 64 [2,1,0] = 66 ∧ Nat.ofDigits 64 [4,4,1,0,0] = 4356 := by
  decide +kernel

noncomputable def v : Fin 3 → ℝ := ![1, 1/2, 0]
noncomputable def z : Fin 3 → ℝ := ![0, 1/2, 1]

theorem toy_plateau (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    overlap (step (2/3) v) (step (2/3) z) (((-2 : ℤ) + u) * (2/3)) = 2/3 := by
  rw [affine _ (by norm_num) v z (-2) u hu hu']
  norm_num [vertex, Fin.sum_univ_three, v, z]
  ring

#print axioms toy_digits
#print axioms toy_plateau
end PearlExample
