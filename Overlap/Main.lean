import Overlap.Numerical
import Overlap.Profile
import Overlap.Spec

namespace Overlap
open MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
attribute [local irreducible] heights events

def nums := heights.items
def width : ℝ := 2 / (N:ℝ)
def h : ℝ → ℝ := step width (values nums D)
def g : ℝ → ℝ := step width (remaining nums D)

theorem num_count : nums.length = N := (Tree.length_items _).trans height_count
theorem num_box (i : Fin nums.length) : nums[i.val] ≤ D :=
  (Tree.le_high (t := heights) (List.getElem_mem _)).trans height_box
theorem num_mass : 2*nums.sum = N*D := by
  rw [nums,Tree.sum_items]; exact height_mass

private theorem width_pos : 0 < width := by norm_num [width,N]
private theorem extent : (nums.length:ℝ)*width = 2 := by rw [num_count]; norm_num [width,N]

theorem complement_h : g = complement h := by
  funext x
  by_cases hx : x ∈ Ico (0:ℝ) 2
  · obtain ⟨i,hi⟩ := cell_at (n := nums.length) width width_pos (extent ▸ hx)
    rw [complement,indicator_of_mem hx,h,g,hi,hi]
    simp only [remaining,values,Nat.cast_sub (num_box i)]
    norm_num [D]; ring
  · rw [complement,indicator_of_notMem hx,g,step_outside _ width_pos _ (extent ▸ hx)]

theorem admissible_h : Admissible h := by
  refine ⟨measurable_step _ _,?_,?_,?_⟩
  · intro x
    by_cases hx : x ∈ Ico (0:ℝ) 2
    · obtain ⟨i,hi⟩ := cell_at (n := nums.length) width width_pos (extent ▸ hx)
      rw [h,hi,values]
      constructor
      · positivity
      · apply (div_le_one (by norm_num [D])).mpr
        exact_mod_cast num_box i
    · rw [h,step_outside _ width_pos _ (extent ▸ hx)]
      norm_num
  · intro x hx; exact step_outside _ width_pos _ (extent ▸ hx)
  · rw [h,mass_step _ width_pos.le,values_sum]
    have m : (2:ℝ)*nums.sum = N*D := by exact_mod_cast num_mass
    norm_num [width,N,D] at m ⊢
    linarith

abbrev U : ℝ := 2462273619527794579322422405079 / 6465103708838880000000000000000

theorem witness_vertex_bound (k : ℤ) : vertex width (values nums D) (remaining nums D) k ≤ U := by
  by_cases low : k ≤ -(nums.length:ℤ)
  · rw [vertex_outside _ _ _ _ (Or.inl low)]; norm_num [U]
  by_cases high : (nums.length:ℤ) ≤ k
  · rw [vertex_outside _ _ _ _ (Or.inr high)]; norm_num [U]
  have hk : (k+(nums.length:ℤ)-1).toNat < 2*nums.length-1 := by omega
  have bound := all_events_le (t := heights) (c := events) (b := B) (d := D) (p := peak)
    (by norm_num [B]) height_box (by rw [height_count]; norm_num [N,D,B])
    event_peak.le (by norm_num [peak,B]) (by rw [height_count]; exact event_count)
    packed_certificate ⟨_,hk⟩
  rw [vertex_event _ _ _ _ (by omega) (by omega)]
  calc
    _ ≤ (peak:ℝ)*(width/(D:ℝ)^2) := by
      apply mul_le_mul_of_nonneg_right _ (by exact div_nonneg width_pos.le (sq_nonneg _))
      exact_mod_cast bound
    _ = U := by norm_num [N,D,peak,width,U]

theorem witness_all_shifts (s : ℝ) : overlap h (complement h) s ≤ U := by
  rw [← complement_h]
  exact continuous_le width width_pos _ _ _ witness_vertex_bound s

theorem witness_supremum_bound :
    sSup (range (overlap h (complement h))) ≤
      2462273619527794579322422405079 / 6465103708838880000000000000000 :=
  csSup_le (range_nonempty _) (forall_mem_range.mpr witness_all_shifts)

theorem witness_peak_value : overlap h (complement h) ((-2284:ℝ)*width) = U := by
  have digits : exactDigits nums D = events.items :=
    digits_certified (b := B) (p := peak) (by norm_num [B]) height_box
      (by rw [height_count]; norm_num [N,D,B]) event_peak.le (by norm_num [peak,B])
      (by rw [height_count]; exact event_count) packed_certificate
  have readDigit := congrArg (fun l : List ℕ => l[7123]?) digits
  change (exactDigits nums D)[7123]? = events.items[7123]? at readDigit
  rw [peak_digit,exactDigits,List.getElem?_ofFn] at readDigit
  have inside : 7123 < 2*nums.length-1 := by rw [num_count]; decide
  simp only [inside, dite_eq_left,Option.some.injEq] at readDigit
  rw [← complement_h]
  change overlap (step width _) (step width _) (((-2284:ℤ):ℝ)*width) = _
  rw [grid_value _ width_pos.le,vertex_event nums D _ (-2284) (by rw [num_count]; decide)
      (by rw [num_count]; decide)]
  rw [show ((-2284:ℤ)+(nums.length:ℤ)-1).toNat = 7123 by rw [num_count]; decide,readDigit]
  norm_num [width,N,D,peak,U]

theorem witness_supremum_exact : sSup (range (overlap h (complement h))) = U := by
  apply le_antisymm witness_supremum_bound
  apply le_csSup ⟨U,forall_mem_range.mpr witness_all_shifts⟩
  exact ⟨_,witness_peak_value⟩

theorem plus_shift_bound (t : ℝ) :
    (∫ x : ℝ, h x * complement h (x+t)) ≤ U := by
  simpa only [overlap,sub_neg_eq_add] using witness_all_shifts (-t)

private theorem objective_nonneg (f : ℝ → ℝ) (hf : Admissible f) :
    0 ≤ sSup (range (overlap f (complement f))) := by
  apply Real.sSup_nonneg
  rintro _ ⟨s,rfl⟩
  apply integral_nonneg
  intro x
  apply mul_nonneg (hf.2.1 x).1
  by_cases hy : x-s ∈ Ico (0:ℝ) 2
  · rw [complement,indicator_of_mem hy]; exact sub_nonneg.mpr (hf.2.1 _).2
  · rw [complement,indicator_of_notMem hy]

theorem continuous_upper_bound : continuousConstant ≤
    2462273619527794579322422405079 / 6465103708838880000000000000000 := by
  refine le_trans (csInf_le (a := sSup (range (overlap h (complement h)))) ?_
    (show ∃ f, Admissible f ∧ _ from ⟨h,admissible_h,rfl⟩)) witness_supremum_bound
  refine ⟨0,?_⟩
  rintro _ ⟨f,hf,rfl⟩; exact objective_nonneg f hf

theorem discrete_upper_bound_of_white {c : ℝ}
    (hc : Tendsto (fun n : ℕ => (minimumOverlap n : ℝ)/n) atTop (𝓝 c))
    (white : WhiteBridge) :
    c ≤ 2462273619527794579322422405079 / 6465103708838880000000000000000 := by
  rw [tendsto_nhds_unique hc white]; exact continuous_upper_bound

#check witness_supremum_exact
#check continuous_upper_bound
#check discrete_upper_bound_of_white
#print axioms admissible_h
#print axioms grid_supremum
#print axioms witness_supremum_exact
#print axioms continuous_upper_bound
#print axioms discrete_upper_bound_of_white
end
end Overlap
