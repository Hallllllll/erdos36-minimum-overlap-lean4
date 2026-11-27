import Overlap.CellApprox
import Overlap.GridLower
import Overlap.LagRounding
import Overlap.Main

namespace Overlap
open Filter Set
open scoped Topology
noncomputable section

/-- A uniform real bound on all signed counts bounds the discrete minimum. -/
private theorem minimum_ratio_le {n : ℕ} (hn : 0 < n) {A : Finset (Fin (2*n))}
    (hA : A.card = n) {b : ℝ} (hb : ∀ k, (multiplicity n A k : ℝ) / n ≤ b) :
    (minimumOverlap n : ℝ) / n ≤ b := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hu (k : ℤ) := (div_le_iff₀ hn').mp (hb k)
  have hmin := (minimumOverlap_le_iff n ⌊b*n⌋₊).mpr ⟨A,hA,fun k => Nat.le_floor (hu k)⟩
  apply (div_le_iff₀ hn').mpr
  exact (Nat.cast_le.mpr hmin).trans (Nat.floor_le ((Nat.cast_nonneg _).trans (hu 0)))

/-- The simultaneous fourth-moment error is eventually below any fixed fraction of n. -/
private theorem eventually_lag_bound {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, lagRoundingBound (2*n) ≤ (δ*(n:ℝ))^4 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (2432 / δ^4)
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with n hn hn₁
  have h : (2432:ℝ) ≤ n*δ^4 := (div_le_iff₀ (pow_pos hδ 4)).mp
    (hN.le.trans (Nat.cast_le.mpr hn))
  have one : (1:ℝ) ≤ n := by exact_mod_cast hn₁
  have hc : Fintype.card (LagConstraint (2*n)) = 4*n := by
    simp [LagConstraint]
    omega
  unfold lagRoundingBound
  rw [hc]
  push_cast
  calc
    _ ≤ 2432*(n:ℝ)^3 := by nlinarith only [mul_nonneg (sq_nonneg (n:ℝ)) (sub_nonneg.mpr one)]
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (n:ℝ)^3)]

private theorem vertex_rescale {m : ℕ} (w : ℝ) (p q : Fin m → ℝ) (k : ℤ) :
    w * vertex 1 p q k = vertex w p q k := by
  rw [mul_comm]
  unfold vertex
  simp only [Finset.sum_mul, mul_one, ite_mul, zero_mul]

/-- Every admissible density bounds all sufficiently large finite minima, up to epsilon. -/
theorem eventually_discrete_le_profile {f : ℝ → ℝ} (hf : Admissible f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (minimumOverlap n : ℝ)/n ≤ sSup (range (overlap f (complement f))) + ε := by
  filter_upwards [exists_cellApprox hf (show 0 < ε/2 by positivity),
    eventually_lag_bound (show 0 < ε/6 by positivity)] with n ha hb
  obtain ⟨hn, p, hp, hmass, hv⟩ := ha
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  obtain ⟨A, hA, _, hcount⟩ := exists_balanced_lag_rounding n p hp hmass
    ((ε/6)*n) (by positivity) hb
  apply minimum_ratio_le hn hA
  intro k
  have hw := div_le_div_of_nonneg_right (hcount k) hn'.le
  rw [add_div, show vertex 1 p (fun i => 1 - p i) k / (n:ℝ) =
    vertex (1/n) p (fun i => 1-p i) k by
      calc
        _ = (1/(n:ℝ))*vertex 1 p (fun i => 1-p i) k := by ring
        _ = _ := vertex_rescale _ _ _ _] at hw
  have hε' : 3*(ε/6*(n:ℝ))/n = ε/2 := by field_simp; ring
  rw [hε'] at hw
  linarith only [hw,hv k]

/-- The upper half of the discrete-to-continuous limit, for the full admissible class. -/
theorem discrete_limsup_le_continuous :
    limsup (fun n : ℕ => (minimumOverlap n : ℝ)/n) atTop ≤ continuousConstant := by
  apply le_csInf (show {q : ℝ | ∃ f : ℝ → ℝ, Admissible f ∧ q =
    sSup (range (overlap f (complement f)))}.Nonempty from ⟨_,h,admissible_h,rfl⟩)
  rintro _ ⟨f,hf,rfl⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop
    (x := (0:ℝ)) (fun n : ℕ => by positivity : ∀ n : ℕ, 0 ≤ (minimumOverlap n : ℝ)/n))
    (eventually_discrete_le_profile hf hε)

/-- The 9,408-cell certificate bounds the discrete limsup, with no bridge premise. -/
theorem discrete_upper_bound :
    limsup (fun n : ℕ => (minimumOverlap n : ℝ)/n) atTop ≤
      2462273619527794579322422405079 / 6465103708838880000000000000000 :=
  discrete_limsup_le_continuous.trans continuous_upper_bound

/-- The balanced discrete minima converge to the infimum over all admissible densities. -/
theorem whiteBridge : WhiteBridge := by
  unfold WhiteBridge
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact ha.trans_le (continuousConstant_le_minimumOverlap_div n hn)
  · intro b hb
    obtain ⟨_, ⟨f,hf,rfl⟩, hfb⟩ := exists_lt_of_csInf_lt
      (show {q : ℝ | ∃ f : ℝ → ℝ, Admissible f ∧
        q = sSup (range (overlap f (complement f)))}.Nonempty from ⟨_,h,admissible_h,rfl⟩) hb
    let v := sSup (range (overlap f (complement f)))
    filter_upwards [eventually_discrete_le_profile hf (show 0 < (b-v)/2 by dsimp [v]; linarith)]
      with n hn
    change (minimumOverlap n : ℝ)/n ≤ v+(b-v)/2 at hn
    change v < b at hfb
    linarith

#print axioms discrete_limsup_le_continuous
#print axioms discrete_upper_bound
#print axioms whiteBridge
end
end Overlap
