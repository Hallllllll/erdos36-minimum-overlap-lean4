import Overlap.AffineBridge

namespace Overlap
open MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

def complement (f : ℝ → ℝ) := (Ico (0:ℝ) 2).indicator (fun x => 1-f x)
def Admissible (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
  (∀ x ∉ Ico (0:ℝ) 2, f x = 0) ∧ (∫ x : ℝ, f x) = 1

def continuousConstant : ℝ :=
  sInf {q : ℝ | ∃ f : ℝ → ℝ, Admissible f ∧ q = sSup (range (overlap f (complement f)))}

/-- Fin (2*n) labels the original sites by 0,...,2*n-1. Translation preserves differences. -/
def multiplicity (n : ℕ) (A : Finset (Fin (2*n))) (k : ℤ) : ℕ :=
  ((A ×ˢ (Finset.univ \ A)).filter (fun p => (p.1.val:ℤ)-p.2.val=k)).card

def minimumOverlap (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A : Finset (Fin (2*n)), A.card = n ∧ m = ⨆ k : ℤ, multiplicity n A k}

/-- This checks the infimum and supremum encodings against the elementary finite problem. -/
theorem minimumOverlap_le_iff (n m : ℕ) : minimumOverlap n ≤ m ↔
    ∃ A : Finset (Fin (2*n)), A.card = n ∧ ∀ k : ℤ, multiplicity n A k ≤ m := by
  let S := {q : ℕ | ∃ A : Finset (Fin (2*n)), A.card = n ∧ q = ⨆ k : ℤ, multiplicity n A k}
  have size : n ≤ (Finset.univ : Finset (Fin (2*n))).card := by simp; omega
  obtain ⟨A,_,hA⟩ := Finset.exists_subset_card_eq size
  have hS : S.Nonempty := ⟨_,A,hA,rfl⟩
  have bounded (A : Finset (Fin (2*n))) : BddAbove (range (multiplicity n A)) := by
    refine ⟨(A ×ˢ (Finset.univ \ A)).card,forall_mem_range.mpr (fun k => ?_)⟩
    exact Finset.card_filter_le _ _
  constructor
  · intro hm
    obtain ⟨A,hA,he⟩ := Nat.sInf_mem hS
    exact ⟨A,hA,fun k => (le_ciSup (bounded A) k).trans (he ▸ hm)⟩
  · rintro ⟨A,hA,hk⟩
    exact (csInf_le (OrderBot.bddBelow _) (show (⨆ k : ℤ, multiplicity n A k) ∈ S from ⟨A,hA,rfl⟩)).trans
      (ciSup_le hk)

/-- The convergence statement of Swinnerton-Dyer's theorem, proved in Haugland (1996).
The continuous objective is given by White (2022), equation (1.1), with the interval and
shift conventions used here. This statement is proved by `Overlap.whiteBridge`. -/
def WhiteBridge : Prop :=
  Tendsto (fun n : ℕ => (minimumOverlap n : ℝ)/n) atTop (𝓝 continuousConstant)

end
end Overlap
