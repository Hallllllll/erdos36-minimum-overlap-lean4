import Overlap.Spec
import Overlap.QuarticRounding

namespace Overlap

open scoped BigOperators

noncomputable section

/-- Ordered pairs of distinct sites at signed lag `k`. -/
def lagEdges (m : ℕ) (k : ℤ) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun e => k ≠ 0 ∧ (e.1.val : ℤ) - e.2.val = k)

/-- The signed-lag multiplicity polynomial, with the zero-lag constraint set to zero. -/
def lagPolynomial {m : ℕ} (k : ℤ) (x : Fin m → ℝ) : ℝ :=
  ∑ e ∈ lagEdges m k, x e.1 * (1 - x e.2)

@[simp] theorem lagPolynomial_zero {m : ℕ} (x : Fin m → ℝ) : lagPolynomial 0 x = 0 := by
  simp [lagPolynomial, lagEdges]

theorem lagPolynomial_eq_vertex {m : ℕ} (x : Fin m → ℝ) (w : ℝ) {k : ℤ} (hk : k ≠ 0) :
    vertex w x (fun i => 1 - x i) k = lagPolynomial k x * w := by
  rw [lagPolynomial, lagEdges, Finset.sum_filter, Finset.sum_mul, Fintype.sum_prod_type]
  unfold vertex
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : (a.val : ℤ) - b.val = k <;> simp [hk, h]

theorem lagPolynomial_outside {m : ℕ} (x : Fin m → ℝ) (k : ℤ)
    (hk : k ≤ -(m : ℤ) ∨ (m : ℤ) ≤ k) : lagPolynomial k x = 0 := by
  by_cases h : k = 0
  · subst k
    exact lagPolynomial_zero x
  · simpa [lagPolynomial_eq_vertex x 1 h] using
      (vertex_outside 1 x (fun i => 1 - x i) k hk)

theorem lagPolynomial_affine {m : ℕ} (k : ℤ) (x : Fin m → ℝ) (i : Fin m) :
    lagPolynomial k x =
      (1 - x i) * lagPolynomial k (Function.update x i 0) +
        x i * lagPolynomial k (Function.update x i 1) := by
  simp only [lagPolynomial, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hl := (Finset.mem_filter.mp he).2
  have hne : e.1 ≠ e.2 := by
    intro h
    exact hl.1 (by simpa [h] using hl.2.symm)
  by_cases ha : e.1 = i
  · have hb : e.2 ≠ i := fun h => hne (ha.trans h.symm)
    simp [ha, Function.update_of_ne hb]
  · by_cases hb : e.2 = i
    · simp [hb, Function.update_of_ne ha]
      ring
    · simp only [Function.update_of_ne ha, Function.update_of_ne hb]
      ring

private theorem lagEdges_incident_card {m : ℕ} (k : ℤ) (i : Fin m) :
    ((lagEdges m k).filter (fun e => e.1 = i ∨ e.2 = i)).card ≤ 2 := by
  let left := (lagEdges m k).filter (fun e => e.1 = i)
  let right := (lagEdges m k).filter (fun e => e.2 = i)
  have split : (lagEdges m k).filter (fun e => e.1 = i ∨ e.2 = i) = left ∪ right := by
    ext e
    simp only [left, right, Finset.mem_filter, Finset.mem_union]
    tauto
  have hleft : left.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro a b ha hb
    obtain ⟨ha, ha'⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hb'⟩ := Finset.mem_filter.mp hb
    have h₁ := (Finset.mem_filter.mp ha).2.2
    have h₂ := (Finset.mem_filter.mp hb).2.2
    rw [ha'] at h₁
    rw [hb'] at h₂
    exact Prod.ext (ha'.trans hb'.symm) (Fin.ext (by omega))
  have hright : right.card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro a b ha hb
    obtain ⟨ha, ha'⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hb'⟩ := Finset.mem_filter.mp hb
    have h₁ := (Finset.mem_filter.mp ha).2.2
    have h₂ := (Finset.mem_filter.mp hb).2.2
    rw [ha'] at h₁
    rw [hb'] at h₂
    exact Prod.ext (Fin.ext (by omega)) (ha'.trans hb'.symm)
  rw [split]
  exact (Finset.card_union_le _ _).trans (by omega)

theorem lagPolynomial_oscillation {m : ℕ} (k : ℤ) (x : Fin m → ℝ) (hx : InCube x)
    (i : Fin m) :
    |lagPolynomial k (Function.update x i 1) - lagPolynomial k (Function.update x i 0)| ≤ 2 := by
  let E := (lagEdges m k).filter (fun e => e.1 = i ∨ e.2 = i)
  let term (b : ℝ) (e : Fin m × Fin m) : ℝ :=
    Function.update x i b e.1 * (1 - Function.update x i b e.2)
  have diff :
      lagPolynomial k (Function.update x i 1) - lagPolynomial k (Function.update x i 0) =
        ∑ e ∈ E, (term 1 e - term 0 e) := by
    rw [lagPolynomial, lagPolynomial, ← Finset.sum_sub_distrib]
    simp only [E, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e.1 = i ∨ e.2 = i
    · simp only [he, ite_true, term]
    · simp only [not_or] at he
      simp [he.1, he.2, Function.update_of_ne]
  have term_box (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1) (e : Fin m × Fin m) :
      term b e ∈ Set.Icc (0 : ℝ) 1 := by
    have hbox (j : Fin m) : Function.update x i b j ∈ Set.Icc (0 : ℝ) 1 := by
      by_cases hj : j = i
      · simpa [hj] using hb
      · simpa [Function.update_of_ne hj] using hx j
    obtain ⟨ha₀, ha₁⟩ := hbox e.1
    obtain ⟨hb₀, hb₁⟩ := hbox e.2
    refine ⟨mul_nonneg ha₀ (sub_nonneg.mpr hb₁), ?_⟩
    exact (mul_le_mul ha₁ (show 1 - Function.update x i b e.2 ≤ 1 by linarith)
      (sub_nonneg.mpr hb₁) zero_le_one).trans_eq (one_mul 1)
  rw [diff]
  calc
    _ ≤ ∑ e ∈ E, |term 1 e - term 0 e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ E, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      obtain ⟨h₁₀, h₁₁⟩ := term_box 1 (by simp) e
      obtain ⟨h₀₀, h₀₁⟩ := term_box 0 (by simp) e
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ = (E.card : ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast lagEdges_incident_card k i

/-- The extra index is total mass. The other indices run through the interior signed lags. -/
abbrev LagConstraint (m : ℕ) := Option (Fin (2 * m - 1))

theorem card_lagConstraint (m : ℕ) : Fintype.card (LagConstraint m) = (2 * m - 1) + 1 := by
  simp [LagConstraint]

/-- Signed lag encoded by an index of the interior lag interval. -/
def signedLag {m : ℕ} (a : Fin (2 * m - 1)) : ℤ := (a.val : ℤ) - ((m : ℤ) - 1)

theorem exists_signedLag {m : ℕ} {k : ℤ} (hlo : -(m : ℤ) < k) (hhi : k < (m : ℤ)) :
    ∃ a : Fin (2 * m - 1), signedLag a = k := by
  let v : ℤ := k + (m : ℤ) - 1
  have hv : 0 ≤ v := by dsimp [v]; omega
  have hcast : (v.toNat : ℤ) = v := Int.toNat_of_nonneg hv
  refine ⟨⟨v.toNat, ?_⟩, ?_⟩
  · dsimp [v] at hcast
    omega
  · simp only [signedLag, hcast]
    dsimp [v]
    omega

def lagConstraint {m : ℕ} (j : LagConstraint m) (x : Fin m → ℝ) : ℝ :=
  match j with
  | none => ∑ i, x i
  | some a => lagPolynomial (signedLag a) x

theorem lagConstraint_affine {m : ℕ} (x : Fin m → ℝ) (_hx : InCube x)
    (i : Fin m) (j : LagConstraint m) :
    lagConstraint j x =
      (1 - x i) * lagConstraint j (Function.update x i 0) +
        x i * lagConstraint j (Function.update x i 1) := by
  cases j with
  | some a => exact lagPolynomial_affine (signedLag a) x i
  | none =>
    simp only [lagConstraint, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : a = i
    · simp [h]
    · simp only [Function.update_of_ne h]
      ring

theorem lagConstraint_oscillation {m : ℕ} (x : Fin m → ℝ) (hx : InCube x)
    (i : Fin m) (j : LagConstraint m) :
    |lagConstraint j (Function.update x i 1) - lagConstraint j (Function.update x i 0)| ≤ 2 := by
  cases j with
  | some a => exact lagPolynomial_oscillation (signedLag a) x hx i
  | none =>
    simp only [lagConstraint, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · norm_num
    · intro a _ ha
      simp [Function.update_of_ne ha]
    · simp

/-- The Boolean vector belonging to a finite set of sites. -/
def lagIndicator {m : ℕ} (S : Finset (Fin m)) (i : Fin m) : ℝ :=
  if i ∈ S then 1 else 0

theorem lagIndicator_inCube {m : ℕ} (S : Finset (Fin m)) : InCube (lagIndicator S) := by
  intro i
  by_cases h : i ∈ S <;> simp [lagIndicator, h]

theorem exists_lagIndicator_of_binary {m : ℕ} (q : Fin m → ℝ)
    (hq : ∀ i, q i = 0 ∨ q i = 1) :
    ∃ S : Finset (Fin m), lagIndicator S = q := by
  classical
  refine ⟨Finset.univ.filter (fun i => q i = 1), ?_⟩
  funext i
  rcases hq i with h | h <;> simp [lagIndicator, h]

@[simp] theorem lagConstraint_mass_indicator {m : ℕ} (S : Finset (Fin m)) :
    lagConstraint none (lagIndicator S) = (S.card : ℝ) := by
  simp [lagConstraint, lagIndicator]

@[simp] theorem lagPolynomial_indicator {n : ℕ} (S : Finset (Fin (2 * n))) (k : ℤ) :
    lagPolynomial k (lagIndicator S) = (multiplicity n S k : ℝ) := by
  have hfilter : ((S ×ˢ (Finset.univ \ S)).filter
      (fun e => (e.1.val : ℤ) - e.2.val = k)) =
        (lagEdges (2 * n) k).filter (fun e => e.1 ∈ S ∧ e.2 ∉ S) := by
    ext e
    simp only [lagEdges, Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨ha, hb⟩, hk⟩
      have hne : e.1 ≠ e.2 := fun h => hb (h ▸ ha)
      refine ⟨⟨?_, hk⟩, ha, hb⟩
      intro hz
      apply hne
      apply Fin.ext
      omega
    · tauto
  rw [multiplicity, hfilter, Finset.card_eq_sum_ones, Nat.cast_sum,
    lagPolynomial, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ha : e.1 ∈ S <;> by_cases hb : e.2 ∈ S <;> simp [lagIndicator, ha, hb]

theorem vertex_lagIndicator {n : ℕ} (S : Finset (Fin (2 * n))) (w : ℝ) (k : ℤ) :
    vertex w (lagIndicator S) (fun i => 1 - lagIndicator S i) k =
      (multiplicity n S k : ℝ) * w := by
  rw [← lagPolynomial_indicator]
  by_cases hk : k = 0
  · subst k
    simp only [lagPolynomial_zero, zero_mul, vertex]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with h
    · have hab : a = b := Fin.ext (by omega)
      subst b
      by_cases ha : a ∈ S <;> simp [lagIndicator, ha]
    · rfl
  · exact lagPolynomial_eq_vertex _ _ hk

theorem lagIndicator_insert_endpoint {m : ℕ} (S : Finset (Fin m)) (i : Fin m) :
    lagIndicator (insert i S) = Function.update (lagIndicator S) i 1 := by
  funext j
  by_cases h : j = i
  · simp [h, lagIndicator]
  · simp [lagIndicator, h]

theorem lagIndicator_zero_endpoint {m : ℕ} (S : Finset (Fin m)) {i : Fin m} (hi : i ∉ S) :
    Function.update (lagIndicator S) i 0 = lagIndicator S := by
  funext j
  by_cases h : j = i
  · simp [h, lagIndicator, hi]
  · exact Function.update_of_ne h _ _

theorem multiplicity_insert_error (n : ℕ) (S : Finset (Fin (2 * n))) (i : Fin (2 * n))
    (k : ℤ) :
    |(multiplicity n (insert i S) k : ℝ) - (multiplicity n S k : ℝ)| ≤ 2 := by
  by_cases hi : i ∈ S
  · simp [Finset.insert_eq_of_mem hi]
  · simpa only [← lagIndicator_insert_endpoint, lagIndicator_zero_endpoint S hi,
      lagPolynomial_indicator] using lagPolynomial_oscillation k (lagIndicator S)
        (lagIndicator_inCube S) i

theorem multiplicity_erase_error (n : ℕ) (S : Finset (Fin (2 * n))) (i : Fin (2 * n))
    (k : ℤ) :
    |(multiplicity n (S.erase i) k : ℝ) - (multiplicity n S k : ℝ)| ≤ 2 := by
  by_cases hi : i ∈ S
  · rw [abs_sub_comm]
    simpa only [Finset.insert_erase hi] using multiplicity_insert_error n (S.erase i) i k
  · simp [Finset.erase_eq_of_notMem hi]

private theorem multiplicity_union_error (n : ℕ) (S D : Finset (Fin (2 * n))) (k : ℤ) :
    |(multiplicity n (S ∪ D) k : ℝ) - (multiplicity n S k : ℝ)| ≤ 2 * (D.card : ℝ) := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert i D hi ih =>
    rw [Finset.union_insert, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ |(multiplicity n (insert i (S ∪ D)) k : ℝ) - (multiplicity n (S ∪ D) k : ℝ)| +
            |(multiplicity n (S ∪ D) k : ℝ) - (multiplicity n S k : ℝ)| := abs_sub_le _ _ _
      _ ≤ 2 + 2 * (D.card : ℝ) := add_le_add (multiplicity_insert_error n (S ∪ D) i k) ih
      _ = _ := by ring

theorem multiplicity_nested_error (n : ℕ) {S T : Finset (Fin (2 * n))} (h : S ⊆ T)
    (k : ℤ) :
    |(multiplicity n T k : ℝ) - (multiplicity n S k : ℝ)| ≤ 2 * ((T.card - S.card : ℕ) : ℝ) := by
  have he : S ∪ (T \ S) = T := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hi | ⟨hi, _⟩)
      · exact h hi
      · exact hi
    · intro hi
      by_cases hs : i ∈ S
      · exact Or.inl hs
      · exact Or.inr ⟨hi, hs⟩
  simpa only [he, Finset.card_sdiff_of_subset h] using multiplicity_union_error n S (T \ S) k

private theorem cast_card_gap (a b : ℕ) :
    (((a - b) + (b - a) : ℕ) : ℝ) = |(a : ℝ) - (b : ℝ)| := by
  by_cases h : b ≤ a
  · have hr : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr hr)]
  · have h' : a ≤ b := by omega
    have hr : (a : ℝ) ≤ b := by exact_mod_cast h'
    rw [Nat.sub_eq_zero_of_le h', zero_add, Nat.cast_sub h', abs_of_nonpos (sub_nonpos.mpr hr)]
    ring

private def firstSites {m : ℕ} (S : Finset (Fin m)) (s : ℕ) : Finset (Fin m) :=
  (S.sort.take s).toFinset

private theorem firstSites_subset {m : ℕ} (S : Finset (Fin m)) (s : ℕ) : firstSites S s ⊆ S := by
  intro i hi
  exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take (List.mem_toFinset.mp hi))

private theorem firstSites_card {m : ℕ} (S : Finset (Fin m)) {s : ℕ} (hs : s ≤ S.card) :
    (firstSites S s).card = s := by
  rw [firstSites, List.toFinset_card_of_nodup ((List.take_sublist _ _).nodup (S.sort_nodup _)),
    List.length_take, Finset.length_sort, Nat.min_eq_left hs]

/-- Keep the first occupied sites when overfull, or add the first vacant sites when underfull. -/
def rebalanceSites (n : ℕ) (S : Finset (Fin (2 * n))) : Finset (Fin (2 * n)) :=
  if n ≤ S.card then firstSites S n else S ∪ firstSites (Finset.univ \ S) (n - S.card)

/-- Balance with exactly the cardinality gap many flips. -/
theorem rebalanceSites_spec (n : ℕ) (S : Finset (Fin (2 * n))) :
    let T := rebalanceSites n S
    T.card = n ∧
      ((S \ T) ∪ (T \ S)).card = (S.card - n) + (n - S.card) ∧
      ∀ k : ℤ, |(multiplicity n T k : ℝ) - (multiplicity n S k : ℝ)| ≤
        2 * |(S.card : ℝ) - (n : ℝ)| := by
  dsimp only [rebalanceSites]
  by_cases h : n ≤ S.card
  · simp only [h, ite_true]
    have hsub := firstSites_subset S n
    have hT := firstSites_card S h
    have hg := cast_card_gap S.card n
    rw [Nat.sub_eq_zero_of_le h, add_zero] at hg ⊢
    refine ⟨hT, ?_, fun k => ?_⟩
    · rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.union_empty,
        Finset.card_sdiff_of_subset hsub, hT]
    · rw [← hg, abs_sub_comm]
      simpa only [hT] using multiplicity_nested_error n hsub k
  · have h' : S.card ≤ n := by omega
    rw [ite_eq_right h]
    have hsize : n - S.card ≤ (Finset.univ \ S).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]
      omega
    let D := firstSites (Finset.univ \ S) (n - S.card)
    have hD : D ⊆ Finset.univ \ S := firstSites_subset _ _
    have hDc : D.card = n - S.card := firstSites_card _ hsize
    have hdisj : Disjoint S D := by
      apply Finset.disjoint_left.mpr
      intro i hi hd
      exact (Finset.mem_sdiff.mp (hD hd)).2 hi
    have hT : (S ∪ D).card = n := by
      rw [Finset.card_union_of_disjoint hdisj, hDc]
      omega
    have hsub : S ⊆ S ∪ D := Finset.subset_union_left
    have hg := cast_card_gap S.card n
    rw [Nat.sub_eq_zero_of_le h', zero_add] at hg ⊢
    refine ⟨hT, ?_, fun k => ?_⟩
    · rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.empty_union,
        Finset.card_sdiff_of_subset hsub, hT]
    · rw [← hg]
      simpa only [hT] using multiplicity_nested_error n hsub k

theorem rebalance_lag (n : ℕ) (S : Finset (Fin (2 * n))) :
    ∃ T : Finset (Fin (2 * n)), T.card = n ∧
      ((S \ T) ∪ (T \ S)).card = (S.card - n) + (n - S.card) ∧
      ∀ k : ℤ, |(multiplicity n T k : ℝ) - (multiplicity n S k : ℝ)| ≤
        2 * |(S.card : ℝ) - (n : ℝ)| :=
  ⟨rebalanceSites n S, rebalanceSites_spec n S⟩

/-- The common fourth-power error bound for the finite lag and mass family. -/
def lagRoundingBound (m : ℕ) : ℝ :=
  (Fintype.card (LagConstraint m) : ℝ) * (128 * (m : ℝ)^2 + 48 * (m : ℝ))

private theorem abs_le_of_fourth_le {z t : ℝ} (ht : 0 ≤ t) (h : z^4 ≤ t^4) :
    |z| ≤ t := by
  by_contra! hn
  have hp := pow_lt_pow_left₀ hn ht (show (4 : ℕ) ≠ 0 by decide)
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ z^4)] at hp
  exact (not_lt_of_ge h) hp

/-- Round the lag and mass constraints together and then rebalance by single-site flips. -/
theorem exists_balanced_lag_rounding (n : ℕ) (p : Fin (2 * n) → ℝ) (hp : InCube p)
    (hmass : (∑ i, p i) = (n : ℝ)) (t : ℝ) (ht : 0 ≤ t)
    (hbound : lagRoundingBound (2 * n) ≤ t^4) :
    ∃ T : Finset (Fin (2 * n)), T.card = n ∧
      (∀ k : ℤ, |(multiplicity n T k : ℝ) - lagPolynomial k p| ≤ 3 * t) ∧
      (∀ k : ℤ, (multiplicity n T k : ℝ) ≤ vertex 1 p (fun i => 1 - p i) k + 3 * t) := by
  obtain ⟨q, hq, hfourth⟩ :=
    round_cube_fourth p hp lagConstraint lagConstraint_affine lagConstraint_oscillation
  obtain ⟨S, rfl⟩ := exists_lagIndicator_of_binary q hq
  have herr (j : LagConstraint (2 * n)) :
      |lagConstraint j (lagIndicator S) - lagConstraint j p| ≤ t := by
    apply abs_le_of_fourth_le ht
    exact (hfourth j).trans (by simpa [lagRoundingBound] using hbound)
  have hS : |(S.card : ℝ) - (n : ℝ)| ≤ t := by
    simpa only [lagConstraint_mass_indicator, show lagConstraint none p = (n : ℝ) from hmass]
      using herr none
  have hlag (k : ℤ) : |(multiplicity n S k : ℝ) - lagPolynomial k p| ≤ t := by
    by_cases h : -((2 * n : ℕ) : ℤ) < k ∧ k < ((2 * n : ℕ) : ℤ)
    · obtain ⟨a, ha⟩ := exists_signedLag h.1 h.2
      simpa only [lagConstraint, ha, lagPolynomial_indicator] using herr (some a)
    · have ho : k ≤ -((2 * n : ℕ) : ℤ) ∨ ((2 * n : ℕ) : ℤ) ≤ k := by omega
      rw [← lagPolynomial_indicator, lagPolynomial_outside _ _ ho, lagPolynomial_outside _ _ ho]
      simpa using ht
  obtain ⟨T, hT, _, hchange⟩ := rebalance_lag n S
  have hTlag (k : ℤ) : |(multiplicity n T k : ℝ) - lagPolynomial k p| ≤ 3 * t := calc
    _ ≤ |(multiplicity n T k : ℝ) - (multiplicity n S k : ℝ)| +
        |(multiplicity n S k : ℝ) - lagPolynomial k p| := abs_sub_le _ _ _
    _ ≤ 2 * |(S.card : ℝ) - (n : ℝ)| + t := add_le_add (hchange k) (hlag k)
    _ ≤ 3 * t := by linarith
  refine ⟨T, hT, hTlag, fun k => ?_⟩
  have hle := (abs_le.mp (hTlag k)).2
  by_cases hk : k = 0
  · subst k
    rw [lagPolynomial_zero] at hle
    have hv : 0 ≤ vertex 1 p (fun i => 1 - p i) 0 := by
      unfold vertex
      apply Finset.sum_nonneg
      intro a _
      apply Finset.sum_nonneg
      intro b _
      split_ifs
      · exact mul_nonneg (mul_nonneg (hp a).1 (sub_nonneg.mpr (hp b).2)) zero_le_one
      · exact le_rfl
    linarith
  · rw [lagPolynomial_eq_vertex p 1 hk, mul_one]
    linarith

end
end Overlap
