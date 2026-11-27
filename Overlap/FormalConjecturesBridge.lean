import Overlap.FormalConjecturesDefs
import Overlap.DiscreteUpper

/-!
# Transfer to Formal Conjectures

Adding one to the internal site labels gives the upstream integer interval and
preserves signed differences. This transports the exact discrete minimum and
the unconditional upper bound.
-/

namespace Overlap

open Filter

private def oneBasedSite (n : ℕ) : Fin (2 * n) ↪ ℤ :=
  ⟨fun i => (i.val : ℤ) + 1, by
    intro i j hij
    apply Fin.ext
    change (i.val : ℤ) + 1 = (j.val : ℤ) + 1 at hij
    omega⟩

private theorem map_univ_oneBasedSite (n : ℕ) :
    (Finset.univ : Finset (Fin (2 * n))).map (oneBasedSite n) =
      Finset.Icc (1 : ℤ) (2 * n) := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_Icc]
  constructor
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    change 1 ≤ (i.val : ℤ) + 1 ∧ (i.val : ℤ) + 1 ≤ 2 * (n : ℤ)
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨⟨(x - 1).toNat, by omega⟩, ?_⟩
    change ((x - 1).toNat : ℤ) + 1 = x
    omega

private theorem overlap_map_oneBasedSite {n : ℕ} (A : Finset (Fin (2 * n))) (k : ℤ) :
    Erdos36.Overlap (A.map (oneBasedSite n)) ((Finset.univ \ A).map (oneBasedSite n)) k =
      multiplicity n A k := by
  rw [Erdos36.Overlap, Finset.product_eq_sprod, ← Finset.prodMap_map_product,
    Finset.filter_map, Finset.card_map, multiplicity]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro p _
  change ((p.1.val : ℤ) + 1) - ((p.2.val : ℤ) + 1) = k ↔
    (p.1.val : ℤ) - p.2.val = k
  omega

private theorem maxOverlap_map_oneBasedSite {n : ℕ} (A : Finset (Fin (2 * n))) :
    Erdos36.MaxOverlap (A.map (oneBasedSite n)) ((Finset.univ \ A).map (oneBasedSite n)) =
      ⨆ k : ℤ, multiplicity n A k := by
  simp only [Erdos36.MaxOverlap, ← overlap_map_oneBasedSite A]

/-- The two encodings minimize the same signed counts for every size, including zero. -/
theorem minimumOverlap_eq_erdos36 (n : ℕ) : minimumOverlap n = Erdos36.M n := by
  unfold minimumOverlap Erdos36.M
  congr 1
  ext m
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨A.map (oneBasedSite n), (Finset.univ \ A).map (oneBasedSite n),
      (Finset.disjoint_map _).2 Finset.disjoint_sdiff, ?_, ?_,
      maxOverlap_map_oneBasedSite A⟩
    · rw [← Finset.map_union, Finset.union_sdiff_of_subset (Finset.subset_univ A),
        map_univ_oneBasedSite]
    · rw [Finset.card_map, Finset.card_map, Finset.card_sdiff_of_subset (Finset.subset_univ A)]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
  · rintro ⟨A, B, hdisj, hunion, hcard, rfl⟩
    have hA : A ⊆ Finset.Icc (1 : ℤ) (2 * n) := hunion ▸ Finset.subset_union_left
    let S : Finset (Fin (2 * n)) := Finset.univ.filter ((· ∈ A) ∘ oneBasedSite n)
    have hS : S.map (oneBasedSite n) = A := by
      dsimp only [S]
      rw [← Finset.filter_map, map_univ_oneBasedSite]
      ext x
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hx => ⟨hA hx, hx⟩⟩
    have hB : (Finset.univ \ S).map (oneBasedSite n) = B := by
      rw [Finset.map_sdiff, map_univ_oneBasedSite, hS, ← hunion,
        Finset.union_sdiff_cancel_left hdisj]
    refine ⟨S, ?_, ?_⟩
    · rw [← hS, ← hB, Finset.card_map, Finset.card_map] at hcard
      have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
      simp only [Finset.card_univ, Fintype.card_fin] at hsum
      omega
    · simpa only [hS, hB] using maxOverlap_map_oneBasedSite S

/-- The exact rational upper bound, expressed with the Formal Conjectures sequence. -/
theorem erdos36_discrete_upper_bound :
    atTop.limsup Erdos36.MinOverlapQuotient ≤
      2462273619527794579322422405079 / 6465103708838880000000000000000 := by
  change atTop.limsup (fun n : ℕ => (Erdos36.M n : ℝ) / n) ≤ _
  simpa only [minimumOverlap_eq_erdos36] using discrete_upper_bound

end Overlap
