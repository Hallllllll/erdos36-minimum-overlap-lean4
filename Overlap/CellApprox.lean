import Overlap.Spec
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Group.Integral

namespace Overlap

open MeasureTheory Set Filter
open scoped BigOperators Function Topology

noncomputable section

private def cell {m : ℕ} (w : ℝ) (i : Fin m) : Set ℝ :=
  Ico ((i.val : ℝ) * w) (((i.val : ℝ) + 1) * w)

private theorem cell_subset {m : ℕ} {w : ℝ} (hw : 0 < w) (i : Fin m) :
    cell w i ⊆ Ico 0 ((m : ℝ) * w) := by
  intro x hx
  have hi : (i.val : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  exact ⟨(mul_nonneg (Nat.cast_nonneg _) hw.le).trans hx.1,
    hx.2.trans_le (mul_le_mul_of_nonneg_right hi hw.le)⟩

private theorem cell_pairwise {m : ℕ} {w : ℝ} (hw : 0 < w) :
    Pairwise (Disjoint on (cell w : Fin m → Set ℝ)) := by
  intro i j hij
  have separated (a b : Fin m) (hab : a.val < b.val) : Disjoint (cell w a) (cell w b) := by
    have hab' : (a.val : ℝ) + 1 ≤ b.val := by exact_mod_cast hab
    exact Set.disjoint_left.mpr fun _ hx hy =>
      (not_lt_of_ge (le_trans (mul_le_mul_of_nonneg_right hab' hw.le) hy.1)) hx.2
  rcases lt_or_gt_of_ne (fun h : i.val = j.val => hij (Fin.ext h)) with h | h
  · exact separated i j h
  · exact (separated j i h).symm

private theorem cell_cover {m : ℕ} {w : ℝ} (hw : 0 < w) :
    (⋃ i : Fin m, cell w i) = Ico 0 ((m : ℝ) * w) := by
  apply Subset.antisymm
  · exact iUnion_subset (cell_subset hw)
  · intro x hx
    have h0 : 0 ≤ x / w := div_nonneg hx.1 hw.le
    have hm : x / w < m := (div_lt_iff₀ hw).mpr hx.2
    let i : Fin m := ⟨⌊x / w⌋₊, (Nat.floor_lt h0).mpr hm⟩
    exact mem_iUnion.mpr ⟨i, (le_div_iff₀ hw).mp (Nat.floor_le h0),
      (div_lt_iff₀ hw).mp (Nat.lt_floor_add_one _)⟩

private theorem step_on_cell {m : ℕ} {w : ℝ} (hw : 0 < w) (p : Fin m → ℝ)
    {i : Fin m} {x : ℝ} (hx : x ∈ cell w i) : step w p x = p i := by
  rw [step, Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    apply indicator_of_notMem
    exact fun hj => Set.disjoint_left.mp (cell_pairwise hw hji) hj hx
  · simp

private theorem step_off_cells {m : ℕ} {w : ℝ} (hw : 0 < w) (p : Fin m → ℝ)
    {x : ℝ} (hx : x ∉ Ico 0 ((m : ℝ) * w)) : step w p x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact indicator_of_notMem (fun hi => hx (cell_subset hw i hi)) _

private theorem cell_volume {m : ℕ} {w : ℝ} (hw : 0 < w) (i : Fin m) :
    volume.real (cell w i) = w := by
  rw [cell, Real.volume_real_Ico, show ((i.val : ℝ) + 1) * w - i.val * w = w by ring,
    max_eq_left hw.le]

private theorem integral_cells {m : ℕ} {w : ℝ} (hw : 0 < w) {u : ℝ → ℝ}
    (hu : Integrable u) :
    (∫ x in Ico 0 ((m : ℝ) * w), u x) = ∑ i : Fin m, ∫ x in cell w i, u x := by
  rw [← cell_cover hw]
  exact integral_iUnion_fintype (fun _ => measurableSet_Ico) (cell_pairwise hw)
    (fun _ => hu.integrableOn)

private theorem integrable_step' {m : ℕ} (w : ℝ) (p : Fin m → ℝ) :
    Integrable (step w p) := by
  apply integrable_finsetSum
  intro i _
  exact (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const measure_Ico_lt_top.ne)

private theorem measurable_step' {m : ℕ} (w : ℝ) (p : Fin m → ℝ) :
    Measurable (step w p) := by
  unfold step bin
  fun_prop (disch := exact measurableSet_Ico)

private theorem integrable_box {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hz : ∀ x ∉ Ico (0 : ℝ) 2, f x = 0) :
    Integrable f := by
  have hi : IntegrableOn f (Ico (0 : ℝ) 2) :=
    IntegrableOn.of_bound measure_Ico_lt_top hf.aestronglyMeasurable 1
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hb x).1] using (hb x).2)
  have he : (Ico (0 : ℝ) 2).indicator f = f := by
    funext x
    by_cases hx : x ∈ Ico (0 : ℝ) 2
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx, hz x hx]
  rw [← he]
  exact hi.integrable_indicator measurableSet_Ico

private def averages {m : ℕ} (w : ℝ) (f : ℝ → ℝ) (i : Fin m) : ℝ :=
  (∫ x in cell w i, f x) / w

private theorem averages_box {m : ℕ} {w : ℝ} (hw : 0 < w) {f : ℝ → ℝ}
    (hi : Integrable f) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (i : Fin m) :
    0 ≤ averages w f i ∧ averages w f i ≤ 1 := by
  refine ⟨div_nonneg (integral_nonneg fun x => (hf x).1) hw.le, (div_le_iff₀ hw).mpr ?_⟩
  rw [one_mul]
  calc
    (∫ x in cell w i, f x) ≤ ∫ _ in cell w i, (1 : ℝ) :=
      setIntegral_mono hi.integrableOn (integrableOn_const measure_Ico_lt_top.ne)
        (fun x => (hf x).2)
    _ = w := by rw [setIntegral_const, cell_volume hw, smul_eq_mul, mul_one]

private theorem averages_mass {n : ℕ} {w : ℝ} (hw : 0 < w)
    (hw' : (n : ℝ) * w = 1) {f : ℝ → ℝ} (hf : Admissible f) (hi : Integrable f) :
    (∑ i : Fin (2 * n), averages w f i) = n := by
  have he : ((2 * n : ℕ) : ℝ) * w = 2 := by push_cast; nlinarith only [hw']
  simp only [averages, ← Finset.sum_div]
  rw [← integral_cells hw hi, he, setIntegral_eq_integral_of_forall_compl_eq_zero hf.2.2.1,
    hf.2.2.2, div_eq_iff hw.ne']
  simpa only [mul_comm] using hw'.symm

/-- On a grid of total width two, taking the complement subtracts each cell value from one. -/
theorem complement_step_of_extent {m : ℕ} {w : ℝ} (hw : 0 < w)
    (he : (m : ℝ) * w = 2) (p : Fin m → ℝ) :
    complement (step w p) = step w (fun i => 1 - p i) := by
  funext x
  by_cases hx : x ∈ Ico (0 : ℝ) 2
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (by rwa [cell_cover hw, he] :
        x ∈ ⋃ i : Fin m, cell w i)
    rw [complement, indicator_of_mem hx, step_on_cell hw p hi, step_on_cell hw _ hi]
  · rw [complement, indicator_of_notMem hx, step_off_cells hw _ (he ▸ hx)]

private theorem step_box {m : ℕ} {w : ℝ} (hw : 0 < w) {p : Fin m → ℝ}
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (x : ℝ) : 0 ≤ step w p x ∧ step w p x ≤ 1 := by
  by_cases hx : x ∈ Ico 0 ((m : ℝ) * w)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (by rwa [cell_cover hw] :
        x ∈ ⋃ i : Fin m, cell w i)
    rw [step_on_cell hw p hi]
    exact hp i
  · rw [step_off_cells hw p hx]
    exact ⟨le_rfl, zero_le_one⟩

/-- A step profile on the full interval is admissible if its entries and total mass are. -/
theorem admissible_step_of_mass {m : ℕ} {w : ℝ} (hw : 0 < w)
    (he : (m : ℝ) * w = 2) {p : Fin m → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hm : w * (∑ i, p i) = 1) : Admissible (step w p) := by
  have hz (x : ℝ) (hx : x ∉ Ico (0 : ℝ) 2) : step w p x = 0 :=
    step_off_cells hw p (he ▸ hx)
  refine ⟨measurable_step' w p, step_box hw hp, hz, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← he,
    integral_cells hw (integrable_step' w p)]
  calc
    _ = ∑ i : Fin m, w * p i := by
      apply Finset.sum_congr rfl
      intro i _
      have hcell : MeasurableSet (cell w i) := measurableSet_Ico
      rw [setIntegral_congr_fun (g := fun _ => p i) (μ := volume) hcell
        (fun _ hx => step_on_cell hw p hx), setIntegral_const, cell_volume hw, smul_eq_mul]
    _ = 1 := by rw [← Finset.mul_sum, hm]

private theorem cell_distance {m : ℕ} {w x y : ℝ} {i : Fin m}
    (hx : x ∈ cell w i) (hy : y ∈ cell w i) : dist x y < w := by
  obtain ⟨hx₁, hx₂⟩ := hx
  obtain ⟨hy₁, hy₂⟩ := hy
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith only [hx₁, hx₂, hy₁, hy₂,
    show ((i.val : ℝ) + 1) * w = i.val * w + w by ring]

private theorem cell_error {m : ℕ} {w δ : ℝ} (hw : 0 < w) (i : Fin m) {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g)
    (hosc : ∀ x ∈ cell w i, ∀ y ∈ cell w i, |g x - g y| ≤ δ) :
    (∫ x in cell w i, |step w (averages (m := m) w f) x - f x|) ≤
      2 * (∫ x in cell w i, |f x - g x|) + w * δ := by
  let C := cell w i
  let e : ℝ → ℝ := fun y => |f y - g y|
  let E : ℝ := ∫ y in C, e y
  have hC : MeasurableSet C := measurableSet_Ico
  have he : Integrable e := (hf.sub hg).abs
  have hc (c : ℝ) : IntegrableOn (fun _ : ℝ => c) C :=
    integrableOn_const measure_Ico_lt_top.ne
  have hconst (c : ℝ) : (∫ _ in C, c) = w * c := by
    rw [setIntegral_const, cell_volume hw, smul_eq_mul]
  -- Average the triangle inequality in y, then integrate in x over the same cell.
  have pointwise (x : ℝ) (hx : x ∈ C) :
      |step w (averages (m := m) w f) x - f x| ≤ e x + (E / w + δ) := by
    rw [step_on_cell hw _ hx, averages]
    have havg : (∫ y in C, f y) / w - f x = (∫ y in C, f y - f x) / w := by
      rw [integral_sub hf.integrableOn (hc (f x)), hconst, sub_div]
      congr 1
      exact (mul_div_cancel_left₀ (f x) hw.ne').symm
    rw [havg, abs_div, abs_of_pos hw, div_le_iff₀ hw]
    calc
      |∫ y in C, f y - f x| ≤ ∫ y in C, |f y - f x| := abs_integral_le_integral_abs
      _ ≤ ∫ y in C, e y + (e x + δ) := by
        apply setIntegral_mono_on (hf.integrableOn.sub (hc (f x))).abs
          (he.integrableOn.add (hc (e x + δ))) hC
        intro y hy
        calc
          |f y - f x| = |(f y - g y) + ((g y - g x) + (g x - f x))| := by
            congr 1
            ring
          _ ≤ |f y - g y| + (|g y - g x| + |g x - f x|) :=
            (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
          _ ≤ e y + (e x + δ) := by
            rw [abs_sub_comm (g x) (f x)]
            dsimp [e]
            linarith only [hosc y hy x hx]
      _ = (e x + (E / w + δ)) * w := by
        rw [integral_add he.integrableOn (hc (e x + δ)), hconst]
        change E + w * (e x + δ) = _
        field_simp
        ring
  calc
    _ ≤ ∫ x in C, e x + (E / w + δ) :=
      setIntegral_mono_on (((integrable_step' w (averages w f)).sub hf).abs.integrableOn)
        (he.integrableOn.add (hc (E / w + δ))) hC pointwise
    _ = 2 * E + w * δ := by
      rw [integral_add he.integrableOn (hc (E / w + δ)), hconst]
      change E + w * (E / w + δ) = _
      field_simp
      ring

private theorem eventually_cell_error {f : ℝ → ℝ} (hf : Admissible f)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      (∫ x, |step (1 / (n : ℝ)) (averages (m := 2 * n) (1 / (n : ℝ)) f) x - f x|) ≤ η := by
  have hfi := integrable_box hf.1 hf.2.1 hf.2.2.1
  -- The continuous approximant is only used to bound oscillation inside cells.
  obtain ⟨g, hg, hgi⟩ := hfi.exists_boundedContinuous_integral_sub_le
    (show 0 < η / 4 by positivity)
  simp only [Real.norm_eq_abs] at hg
  obtain ⟨d, hd, hosc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (s := Icc (0 : ℝ) 2)
      g.continuous.continuousOn) (η / 4) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / d)
  apply eventually_atTop.mpr
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn₀ : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N 1).trans hn)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn₀
  let w := 1 / (n : ℝ)
  have hw : 0 < w := by dsimp [w]; positivity
  have hwd : w < d := by
    apply (div_lt_iff₀ hnR).mpr
    rw [mul_comm]
    exact (div_lt_iff₀ hd).mp (hN.trans_le (by exact_mod_cast (le_max_left N 1).trans hn))
  have hwN : ((2 * n : ℕ) : ℝ) * w = 2 := by push_cast; dsimp [w]; field_simp
  have hgi' : Integrable (fun x => |f x - g x|) := (hfi.sub hgi).abs
  have herror : Integrable (fun x => |step w (averages (m := 2 * n) w f) x - f x|) :=
    ((integrable_step' w (averages (m := 2 * n) w f)).sub hfi).abs
  refine ⟨hn₀, ?_⟩
  change (∫ x, |step w (averages (m := 2 * n) w f) x - f x|) ≤ η
  have hcut : (∫ x in Ico (0 : ℝ) 2, |step w (averages (m := 2 * n) w f) x - f x|) =
      ∫ x, |step w (averages (m := 2 * n) w f) x - f x| := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [step_off_cells hw _ (hwN ▸ hx), hf.2.2.1 x hx, sub_self, abs_zero]
  have hrestrict : (∫ x in Ico (0 : ℝ) 2, |f x - g x|) ≤ η / 4 :=
    (setIntegral_le_integral hgi' (ae_of_all _ fun _ => abs_nonneg _)).trans hg
  rw [← hcut, ← hwN, integral_cells hw herror]
  calc
    _ ≤ ∑ i : Fin (2 * n), (2 * (∫ x in cell w i, |f x - g x|) + w * (η / 4)) := by
      apply Finset.sum_le_sum
      intro i _
      apply cell_error hw i hfi hgi
      intro x hx y hy
      have hc {z : ℝ} (hz : z ∈ cell w i) : z ∈ Icc (0 : ℝ) 2 :=
        Ico_subset_Icc_self (hwN ▸ cell_subset hw i hz)
      exact (Real.dist_eq _ _ ▸ hosc x (hc hx) y (hc hy)
        ((cell_distance hx hy).trans hwd)).le
    _ = 2 * (∫ x in Ico (0 : ℝ) 2, |f x - g x|) + 2 * (η / 4) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← integral_cells hw hgi', hwN]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, hwN]
    _ ≤ η := by linarith only [hrestrict]

/-- The truncated complement preserves the pointwise bounds. -/
theorem complement_box {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (x : ℝ) : 0 ≤ complement f x ∧ complement f x ≤ 1 := by
  by_cases hx : x ∈ Ico (0 : ℝ) 2
  · rw [complement, indicator_of_mem hx]
    exact ⟨sub_nonneg.mpr (hf x).2, sub_le_self _ (hf x).1⟩
  · rw [complement, indicator_of_notMem hx]
    exact ⟨le_rfl, zero_le_one⟩

private theorem overlap_integrable' {f : ℝ → ℝ} (hf : Integrable f) {g : ℝ → ℝ}
    (hg : Measurable g) (hb : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (s : ℝ) :
    Integrable (fun x => f x * complement g (x - s)) := by
  have hm : Measurable (complement g) := (measurable_const.sub hg).indicator measurableSet_Ico
  exact hf.mul_bdd (hm.comp (measurable_id.sub_const s)).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (complement_box hb _).1]
      exact (complement_box hb (x - s)).2)

private theorem overlap_stability {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (s : ℝ) :
    overlap f (complement f) s ≤
      overlap g (complement g) s + 2 * ∫ x, |f x - g x| := by
  let e : ℝ → ℝ := fun x => |f x - g x|
  have he : Integrable e := (hf.sub hg).abs
  have hes : Integrable (fun x => e (x - s)) := he.comp_sub_right s
  have hc (x : ℝ) : |complement f x - complement g x| ≤ e x := by
    by_cases hx : x ∈ Ico (0 : ℝ) 2
    · simp only [complement, indicator_of_mem hx, e]
      rw [show 1 - f x - (1 - g x) = g x - f x by ring, abs_sub_comm]
    · simp only [complement, indicator_of_notMem hx, sub_self, abs_zero]
      exact abs_nonneg _
  have hp (x : ℝ) : f x * complement f (x - s) - g x * complement g (x - s) ≤
      e x + e (x - s) := by
    let y := x - s
    calc
      _ = (f x - g x) * complement f y + g x * (complement f y - complement g y) := by
        dsimp [y]
        ring
      _ ≤ e x * complement f y + g x * |complement f y - complement g y| :=
        add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) (complement_box hfb y).1)
          (mul_le_mul_of_nonneg_left (le_abs_self _) (hgb x).1)
      _ ≤ e x * 1 + 1 * e y :=
        add_le_add (mul_le_mul_of_nonneg_left (complement_box hfb y).2 (abs_nonneg _))
          (mul_le_mul (hgb x).2 (hc y) (abs_nonneg _) zero_le_one)
      _ = _ := by rw [mul_one, one_mul]
  have h := integral_mono ((overlap_integrable' hf hfm hfb s).sub
    (overlap_integrable' hg hgm hgb s)) (he.add hes) hp
  change (∫ x, f x * complement f (x - s) - g x * complement g (x - s)) ≤
    ∫ x, e x + e (x - s) at h
  -- Translation invariance makes the error bound independent of the shift.
  rw [integral_sub (overlap_integrable' hf hfm hfb s) (overlap_integrable' hg hgm hgb s),
    integral_add he hes, integral_sub_right_eq_self e s] at h
  unfold overlap
  dsimp [e] at h
  linarith only [h]

private theorem admissible_overlap_le_sup {f : ℝ → ℝ} (hf : Admissible f) (s : ℝ) :
    overlap f (complement f) s ≤ sSup (range (overlap f (complement f))) := by
  have hi := integrable_box hf.1 hf.2.1 hf.2.2.1
  apply le_csSup _ (mem_range_self s)
  refine ⟨1, forall_mem_range.mpr fun t => ?_⟩
  rw [← hf.2.2.2]
  exact integral_mono (overlap_integrable' hi hf.1 hf.2.1 t) hi
    (fun x => mul_le_of_le_one_right (hf.2.1 x).1 (complement_box hf.2.1 _).2)

/-- Cell averages give exact mass and a uniform upper bound over all real shifts. -/
theorem exists_cellApprox_all_shifts {f : ℝ → ℝ} (hf : Admissible f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      ∃ p : Fin (2 * n) → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ (∑ i, p i) = (n : ℝ) ∧
        ∀ s : ℝ, overlap (step (1 / (n : ℝ)) p) (step (1 / (n : ℝ)) (fun i => 1 - p i)) s ≤
          sSup (range (overlap f (complement f))) + ε := by
  filter_upwards [eventually_cell_error hf (show 0 < ε / 2 by positivity)] with n hn
  obtain ⟨hn, herr⟩ := hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let w := 1 / (n : ℝ)
  have hw : 0 < w := by dsimp [w]; positivity
  have hw' : (n : ℝ) * w = 1 := by dsimp [w]; field_simp
  have he : ((2 * n : ℕ) : ℝ) * w = 2 := by push_cast; nlinarith only [hw']
  let p : Fin (2 * n) → ℝ := averages w f
  have hi := integrable_box hf.1 hf.2.1 hf.2.2.1
  have hp := averages_box hw hi hf.2.1 (m := 2 * n)
  refine ⟨hn, p, hp, averages_mass hw hw' hf hi, fun s => ?_⟩
  change overlap (step w p) (step w (fun i => 1 - p i)) s ≤ _
  rw [← complement_step_of_extent hw he p]
  have hs := overlap_stability (integrable_step' w p) hi (measurable_step' w p) hf.1
    (step_box hw hp) hf.2.1 s
  exact hs.trans (add_le_add (admissible_overlap_le_sup hf s) (by linarith only [herr]))

/-- The even grid has an exact-mass fractional vector with all its vertex values bounded. -/
theorem exists_cellApprox {f : ℝ → ℝ} (hf : Admissible f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      ∃ p : Fin (2 * n) → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧ (∑ i, p i) = (n : ℝ) ∧
        ∀ k : ℤ, vertex (1 / (n : ℝ)) p (fun i => 1 - p i) k ≤
          sSup (range (overlap f (complement f))) + ε := by
  filter_upwards [exists_cellApprox_all_shifts hf hε] with n hn
  obtain ⟨hn, p, hp, hm, hs⟩ := hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw : 0 ≤ 1 / (n : ℝ) := by positivity
  refine ⟨hn, p, hp, hm, fun k => ?_⟩
  rw [← grid_value _ hw]
  exact hs _

#print axioms exists_cellApprox_all_shifts
#print axioms exists_cellApprox

end
end Overlap
