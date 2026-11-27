import Overlap.AffineBridge
import Overlap.Algebra

namespace Overlap
open MeasureTheory Set
open scoped BigOperators
noncomputable section

theorem step_outside {n : ℕ} (w : ℝ) (hw : 0 < w) (v : Fin n → ℝ)
    {x : ℝ} (hx : x ∉ Ico 0 ((n:ℝ)*w)) : step w v x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro h
  have hi : (i.val:ℝ)+1 ≤ n := by exact_mod_cast i.isLt
  exact hx ⟨(mul_nonneg (Nat.cast_nonneg _) hw.le).trans h.1,
    h.2.trans_le (mul_le_mul_of_nonneg_right hi hw.le)⟩

theorem cell_at {n : ℕ} (w : ℝ) (hw : 0 < w) {x : ℝ}
    (hx : x ∈ Ico 0 ((n:ℝ)*w)) :
    ∃ i : Fin n, ∀ v : Fin n → ℝ, step w v x = v i := by
  have x0 : 0 ≤ x/w := div_nonneg hx.1 hw.le
  have xn : x/w < n := (div_lt_iff₀ hw).mpr hx.2
  let i : Fin n := ⟨⌊x/w⌋₊,(Nat.floor_lt x0).mpr xn⟩
  have lo : (i.val:ℝ)*w ≤ x := (le_div_iff₀ hw).mp (Nat.floor_le x0)
  have hi : x < ((i.val:ℝ)+1)*w := (div_lt_iff₀ hw).mp (Nat.lt_floor_add_one _)
  refine ⟨i,fun v => ?_⟩
  rw [step,Finset.sum_eq_single i]
  · unfold bin
    rw [indicator_of_mem (show x ∈ Ico ((i.val:ℝ)*w) (((i.val:ℝ)+1)*w) from ⟨lo,hi⟩)]
  · intro j _ he
    apply indicator_of_notMem
    intro hj
    have jlo := (le_div_iff₀ hw).mpr hj.1
    have jhi := (div_lt_iff₀ hw).mpr hj.2
    apply he
    exact Fin.ext (by exact_mod_cast (Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ x/w)).mpr ⟨jlo,jhi⟩ |>.symm)
  · simp

theorem measurable_step {n : ℕ} (w : ℝ) (v : Fin n → ℝ) : Measurable (step w v) := by
  unfold step bin
  fun_prop (disch := exact measurableSet_Ico)

theorem mass_step {n : ℕ} (w : ℝ) (hw : 0 ≤ w) (v : Fin n → ℝ) :
    (∫ x : ℝ, step w v x) = w * ∑ i, v i := by
  unfold step
  rw [integral_finsetSum,Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [bin,integral_indicator_const _ measurableSet_Ico,Real.volume_real_Ico,smul_eq_mul]
    rw [show ((i.val:ℝ)+1)*w-i.val*w=w by ring,max_eq_left hw]
  · intro i _
    apply (integrable_indicator_iff measurableSet_Ico).mpr
    exact integrableOn_const measure_Ico_lt_top.ne

def values (a : List ℕ) (d : ℕ) (i : Fin a.length) : ℝ := (a[i.val]:ℝ)/d
def remaining (a : List ℕ) (d : ℕ) (i : Fin a.length) : ℝ := ((d-a[i.val]:ℕ):ℝ)/d

theorem values_sum (a : List ℕ) (d : ℕ) :
    ∑ i, values a d i = (a.sum:ℝ)/d := by
  have ho : Nat.ofDigits 1 a = a.sum := by induction a <;> simp_all [Nat.ofDigits]
  have hn := digits_sum a 1
  simp only [one_pow,mul_one,ho] at hn
  simp only [values,← Finset.sum_div,← Nat.cast_sum,← hn]

theorem vertex_event (a : List ℕ) (d : ℕ) (w : ℝ) (k : ℤ)
    (hk : -(a.length:ℤ) < k) (_hk' : k < (a.length:ℤ)) :
    vertex w (values a d) (remaining a d) k =
      (event a d (k+(a.length:ℤ)-1).toNat:ℝ) * (w / (d:ℝ)^2) := by
  simp only [event,vertex,values,remaining,Nat.cast_sum,Nat.cast_ite,Nat.cast_mul,Nat.cast_zero,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have same : (i.val:ℤ)-j.val=k ↔ i.val+(a.length-1-j.val)=(k+(a.length:ℤ)-1).toNat := by
    have := i.isLt; have := j.isLt; omega
  by_cases h : (i.val:ℤ)-j.val=k
  · simp only [ite_eq_left h,ite_eq_left (same.mp h)]
    ring
  · simp only [ite_eq_right h,ite_eq_right (mt same.mpr h),zero_mul]

end
end Overlap
