import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

namespace Overlap
open MeasureTheory Set
open scoped BigOperators
noncomputable section

def bin (w : ℝ) (i : ℕ) (v x : ℝ) : ℝ :=
  (Ico ((i:ℝ)*w) (((i:ℝ)+1)*w)).indicator (fun _ => v) x

def step {n : ℕ} (w : ℝ) (v : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, bin w i.val (v i) x

def overlap (f g : ℝ → ℝ) (s : ℝ) := ∫ x : ℝ, f x * g (x-s)

def leftEnd (w : ℝ) (i j : ℕ) (s : ℝ) := max ((i:ℝ)*w) ((j:ℝ)*w+s)
def rightEnd (w : ℝ) (i j : ℕ) (s : ℝ) := min (((i:ℝ)+1)*w) (((j:ℝ)+1)*w+s)

theorem pair_fun (w : ℝ) (i j : ℕ) (v z s : ℝ) :
    (fun x => bin w i v x * bin w j z (x-s)) =
    (Ico (leftEnd w i j s) (rightEnd w i j s)).indicator (fun _ => v*z) := by
  funext x
  simp only [bin,Set.indicator, mem_Ico,leftEnd,rightEnd,max_le_iff,lt_min_iff]
  split_ifs <;> simp_all <;> grind (splits := 8)

theorem pair_integrable (w : ℝ) (i j : ℕ) (v z s : ℝ) :
    Integrable (fun x => bin w i v x * bin w j z (x-s)) := by
  rw [pair_fun, integrable_indicator_iff measurableSet_Ico]
  exact integrableOn_const measure_Ico_lt_top.ne

theorem pair_int (w : ℝ) (i j : ℕ) (v z s : ℝ) :
    (∫ x : ℝ, bin w i v x * bin w j z (x-s)) =
    (v*z)*max (rightEnd w i j s-leftEnd w i j s) 0 := by
  rw [pair_fun, integral_indicator_const _ measurableSet_Ico,Real.volume_real_Ico]
  simp [smul_eq_mul,mul_comm]

theorem scaled_length (w : ℝ) (hw : 0 ≤ w) (i j : ℕ) (s : ℝ) :
    max (rightEnd w i j (s*w)-leftEnd w i j (s*w)) 0 =
    max (min ((i:ℝ)+1) ((j:ℝ)+1+s) - max (i:ℝ) ((j:ℝ)+s)) 0 * w := by
  simp only [rightEnd,leftEnd,← add_mul,← min_mul_of_nonneg _ _ hw,
    ← max_mul_of_nonneg _ _ hw,← sub_mul]
  rw [max_mul_of_nonneg _ _ hw,zero_mul]

theorem unit_length (i j : ℕ) (k : ℤ) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    max (min ((i:ℝ)+1) ((j:ℝ)+1+(k+u)) - max (i:ℝ) ((j:ℝ)+(k+u))) 0 =
      (if (i:ℤ)-j = k then 1-u else 0) +
      (if (i:ℤ)-j = k+1 then u else 0) := by
  by_cases h : (i:ℤ)-j = k
  · have h' : (i:ℝ)-(j:ℝ) = (k:ℝ) := by exact_mod_cast h
    simp only [h, ite_true, ite_false, add_zero, show k ≠ k+1 by omega, min_def, max_def]
    split_ifs <;> linarith
  by_cases h' : (i:ℤ)-j = k+1
  · have hr : (i:ℝ)-(j:ℝ) = (k:ℝ)+1 := by exact_mod_cast h'
    simp only [ite_eq_right h,ite_eq_left h',zero_add,min_def,max_def]
    split_ifs <;> linarith
  have hsplit : (i:ℤ)-j+1 ≤ k ∨ k+2 ≤ (i:ℤ)-j := by omega
  simp only [ite_eq_right h,ite_eq_right h',zero_add,min_def,max_def]
  rcases hsplit with hlow | hhigh
  · have hr : (i:ℝ)-(j:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast hlow
    split_ifs <;> linarith
  · have hr : (k:ℝ)+2 ≤ (i:ℝ)-(j:ℝ) := by exact_mod_cast hhigh
    split_ifs <;> linarith

def vertex {n : ℕ} (w : ℝ) (v z : Fin n → ℝ) (k : ℤ) : ℝ :=
  ∑ i, ∑ j, if (i.val:ℤ)-j.val=k then v i*z j*w else 0

theorem affine {n : ℕ} (w : ℝ) (hw : 0 ≤ w) (v z : Fin n → ℝ)
    (k : ℤ) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    overlap (step w v) (step w z) ((k+u)*w) =
      (1-u)*vertex w v z k + u*vertex w v z (k+1) := by
  simp only [overlap,step,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun j _ => pair_integrable _ _ _ _ _ _),pair_int]
    simp only [scaled_length _ hw,unit_length _ _ _ _ hu hu',vertex,Finset.mul_sum,← Finset.sum_add_distrib]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  · intro i _
    exact integrable_finsetSum _ (fun j _ => pair_integrable _ _ _ _ _ _)

theorem floor_partition (s w : ℝ) (hw : 0 < w) :
    ∃ (k : ℤ) (u : ℝ), 0 ≤ u ∧ u ≤ 1 ∧ s = ((k:ℝ)+u)*w := by
  refine ⟨⌊s/w⌋, s/w-⌊s/w⌋, sub_nonneg.mpr (Int.floor_le _), ?_, ?_⟩
  · have := Int.lt_floor_add_one (s/w); linarith
  · field_simp; ring

theorem continuous_le {n : ℕ} (w : ℝ) (hw : 0 < w) (v z : Fin n → ℝ)
    (U : ℝ) (hv : ∀ k : ℤ, vertex w v z k ≤ U) (s : ℝ) :
    overlap (step w v) (step w z) s ≤ U := by
  obtain ⟨k,u,h0,h1,rfl⟩ := floor_partition s w hw
  rw [affine _ hw.le _ _ _ _ h0 h1]
  calc
    _ ≤ (1-u)*U+u*U := add_le_add
      (mul_le_mul_of_nonneg_left (hv k) (by linarith))
      (mul_le_mul_of_nonneg_left (hv (k+1)) h0)
    _ = _ := by ring

theorem grid_value {n : ℕ} (w : ℝ) (hw : 0 ≤ w) (v z : Fin n → ℝ) (k : ℤ) :
    overlap (step w v) (step w z) (k*w) = vertex w v z k := by
  simpa using affine w hw v z k 0 (by norm_num) (by norm_num)

theorem vertex_outside {n : ℕ} (w : ℝ) (v z : Fin n → ℝ) (k : ℤ)
    (hk : k ≤ -(n:ℤ) ∨ (n:ℤ) ≤ k) : vertex w v z k = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  exact ite_eq_right (by have := i.isLt; have := j.isLt; omega)

theorem grid_supremum {n : ℕ} (w : ℝ) (hw : 0 < w) (v z : Fin n → ℝ) :
    ∃ k ∈ Finset.Icc (-(n:ℤ)) (n:ℤ),
      (∀ j ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), vertex w v z j ≤ vertex w v z k) ∧
      sSup (Set.range (overlap (step w v) (step w z))) = vertex w v z k := by
  let K := Finset.Icc (-(n:ℤ)) (n:ℤ)
  have hn : (n:ℤ) ∈ K := Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩
  obtain ⟨k,hk,hm⟩ := Finset.exists_max_image K (vertex w v z) ⟨_,hn⟩
  have allK : ∀ j : ℤ, vertex w v z j ≤ vertex w v z k := by
    intro j
    by_cases hj : j ∈ K
    · exact hm j hj
    · have ho : j ≤ -(n:ℤ) ∨ (n:ℤ) ≤ j := by
        simp only [K,Finset.mem_Icc] at hj
        omega
      rw [vertex_outside _ _ _ _ ho, ← vertex_outside w v z (n:ℤ) (Or.inr le_rfl)]
      exact hm _ hn
  have upper := continuous_le w hw v z _ allK
  refine ⟨k,hk,hm, le_antisymm (csSup_le (Set.range_nonempty _) ?_) ?_⟩
  · rintro _ ⟨s,rfl⟩; exact upper s
  · rw [← grid_value w hw.le v z k]
    exact le_csSup ⟨_,Set.forall_mem_range.mpr upper⟩ ⟨_,rfl⟩

end
end Overlap
