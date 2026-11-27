import Overlap.CellApprox

namespace Overlap

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- The grid values of the indicator of a set of sites. -/
def gridIndicator {m : ℕ} (A : Finset (Fin m)) (i : Fin m) : ℝ :=
  if i ∈ A then 1 else 0

private theorem gridIndicator_sum {m : ℕ} (A : Finset (Fin m)) :
    (∑ i, gridIndicator A i) = (A.card : ℝ) := by
  classical
  have hfilter : (Finset.univ : Finset (Fin m)).filter (· ∈ A) = A := by
    ext i
    simp
  simp only [gridIndicator]
  rw [← Finset.sum_filter, hfilter]
  simp

/-- At a grid vertex, the product of the two indicators counts the pairs with that difference. -/
theorem vertex_gridIndicator (n : ℕ) (A : Finset (Fin (2 * n))) (w : ℝ) (k : ℤ) :
    vertex w (gridIndicator A) (fun i => 1 - gridIndicator A i) k =
      (multiplicity n A k : ℝ) * w := by
  classical
  let P : Finset (Fin (2 * n) × Fin (2 * n)) := Finset.univ ×ˢ Finset.univ
  let R (p : Fin (2 * n) × Fin (2 * n)) : Prop :=
    p.1 ∈ A ∧ p.2 ∉ A ∧ (p.1.val : ℤ) - p.2.val = k
  have hfilter : P.filter R =
      (A ×ˢ (Finset.univ \ A)).filter (fun p => (p.1.val : ℤ) - p.2.val = k) := by
    ext p
    simp [P, R, Finset.mem_sdiff, and_assoc]
  calc
    vertex w (gridIndicator A) (fun i => 1 - gridIndicator A i) k =
        ∑ p ∈ P, if R p then w else 0 := by
      simp only [P, Finset.sum_product, vertex]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [R, gridIndicator, hi, hj]
    _ = (multiplicity n A k : ℝ) * w := by
      rw [← Finset.sum_filter, hfilter]
      simp [multiplicity, nsmul_eq_mul]

private theorem objectives_bddBelow :
    BddBelow {q : ℝ | ∃ f : ℝ → ℝ, Admissible f ∧
      q = sSup (range (overlap f (complement f)))} := by
  refine ⟨0, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  apply Real.sSup_nonneg
  rintro _ ⟨s, rfl⟩
  exact integral_nonneg (fun x => mul_nonneg (hf.2.1 x).1 (complement_box hf.2.1 _).1)

/-- A balanced discrete minimizer yields an admissible continuum profile. -/
theorem continuousConstant_le_minimumOverlap_div (n : ℕ) (hn : 0 < n) :
    continuousConstant ≤ (minimumOverlap n : ℝ) / n := by
  obtain ⟨A, hA, hk⟩ := (minimumOverlap_le_iff n (minimumOverlap n)).mp le_rfl
  let w : ℝ := 1 / (n : ℝ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : 0 < w := by dsimp [w]; positivity
  have hmass : w * (n : ℝ) = 1 := by dsimp [w]; field_simp
  have he : ((2 * n : ℕ) : ℝ) * w = 2 := by push_cast; nlinarith only [hmass]
  have hf : Admissible (step w (gridIndicator A)) := by
    apply admissible_step_of_mass hw he
    · intro i
      by_cases hi : i ∈ A <;> simp [gridIndicator, hi]
    · rw [gridIndicator_sum, hA, hmass]
  have hv (k : ℤ) :
      vertex w (gridIndicator A) (fun i => 1 - gridIndicator A i) k ≤
        (minimumOverlap n : ℝ) / n := by
    rw [vertex_gridIndicator, show (minimumOverlap n : ℝ) / n = (minimumOverlap n : ℝ) * w by
      simp [w, div_eq_mul_inv]]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk k) hw.le
  refine (csInf_le objectives_bddBelow ⟨step w (gridIndicator A), hf, rfl⟩).trans ?_
  apply csSup_le (range_nonempty _)
  refine forall_mem_range.mpr fun s => ?_
  rw [complement_step_of_extent hw he]
  exact continuous_le w hw _ _ _ hv s

#print axioms vertex_gridIndicator
#print axioms continuousConstant_le_minimumOverlap_div

end
end Overlap
