import Overlap.PackedConvolution
import Mathlib.Data.Fin.Rev

set_option backward.isDefEq.respectTransparency false
namespace Overlap
open scoped BigOperators

namespace Tree

@[simp] theorem sum_items (t : Tree) : t.items.sum = t.total := by
  induction t with
  | leaf => simp [items, total]
  | node l r hl hr => simp [items, total, hl, hr]

theorem other_eq (t : Tree) (b d : ℕ) :
    t.other b d = Nat.ofDigits b ((t.items.map (d-·)).reverse) := by
  induction t with
  | leaf x => simp [other,items]
  | node l r hl hr => simp [other,items,Nat.ofDigits_append,hl,hr]

end Tree

/-- Reindex a sum over the reversed complements by their positions in the original list. -/
private theorem sum_reverse_complements (a : List ℕ) (d : ℕ) (f : ℕ → ℕ → ℕ) :
    (∑ j : Fin ((a.map (d-·)).reverse).length, f j.val ((a.map (d-·)).reverse)[j.val]) =
      ∑ j : Fin a.length, f (a.length - 1 - j.val) (d - a[j.val]) := by
  let e : Fin a.length ≃ Fin ((a.map (d-·)).reverse).length :=
    Fin.revPerm.trans (finCongr (by simp))
  symm
  apply Fintype.sum_equiv e
  intro j
  have he : (e j).val = a.length - 1 - j.val := by
    change j.rev.val = _
    simp only [Fin.val_rev]
    omega
  have hrev : a.length - 1 - (a.length - 1 - j.val) = j.val := by
    have hj := j.isLt
    omega
  simp only [he, List.getElem_reverse, List.getElem_map, List.length_map, hrev]

theorem reverse_sum (a : List ℕ) (b d : ℕ) :
    Nat.ofDigits b ((a.map (d-·)).reverse) =
      ∑ i : Fin a.length, (d-a[i.val])*b^(a.length-1-i.val) := by
  rw [digits_sum]
  exact sum_reverse_complements a d (fun i x => x * b ^ i)

def event (a : List ℕ) (d k : ℕ) : ℕ :=
  ∑ i : Fin a.length, ∑ j : Fin a.length,
    if i.val + (a.length-1-j.val) = k then a[i.val]*(d-a[j.val]) else 0

def exactDigits (a : List ℕ) (d : ℕ) : List ℕ :=
  List.ofFn fun k : Fin (2*a.length-1) => event a d k.val

/-- The overlap event is the ordinary convolution coefficient against the reversed complements. -/
theorem event_eq_coeff (a : List ℕ) (d k : ℕ) :
    event a d k = PackedConvolution.coeff a ((a.map (d-·)).reverse) k := by
  unfold event PackedConvolution.coeff
  apply Finset.sum_congr rfl
  intro i _
  symm
  exact sum_reverse_complements a d (fun j y => if i.val + j = k then a[i.val] * y else 0)

private theorem overlap_outputLength (a : List ℕ) (d : ℕ) :
    PackedConvolution.outputLength a.length ((a.map (d-·)).reverse).length =
      2 * a.length - 1 := by
  simp only [List.length_reverse, List.length_map, PackedConvolution.outputLength, or_self]
  split <;> omega

theorem exactDigits_eq_convolution (a : List ℕ) (d : ℕ) :
    exactDigits a d = PackedConvolution.convolution a ((a.map (d-·)).reverse) := by
  unfold exactDigits PackedConvolution.convolution
  simp only [event_eq_coeff]
  exact (List.ofFn_congr (overlap_outputLength a d)
    (fun k => PackedConvolution.coeff a ((a.map (d-·)).reverse) k.val)).symm

theorem event_lt {a : List ℕ} {d b : ℕ} (ha : ∀ x ∈ a, x ≤ d)
    (hb : a.length*a.length*d*d < b) (k : ℕ) : event a d k < b := by
  rw [event_eq_coeff]
  refine PackedConvolution.coeff_lt ha (yMax := d) ?_ ?_ k
  · intro y hy
    rw [List.mem_reverse] at hy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
    exact Nat.sub_le _ _
  · simpa only [List.length_reverse, List.length_map] using hb

theorem packed_events (a : List ℕ) (b d : ℕ) :
    Nat.ofDigits b (exactDigits a d) =
      Nat.ofDigits b a * Nat.ofDigits b ((a.map (d-·)).reverse) := by
  rw [exactDigits_eq_convolution, PackedConvolution.packed]

theorem digits_certified {t c : Tree} {b d p : ℕ} (hB : 1 < b)
    (hbox : t.high ≤ d) (hsize : t.size*t.size*d*d < b)
    (hc : c.high ≤ p) (hp : p < b) (hn : c.size = 2*t.size-1)
    (hm : t.pack b*t.other b d = c.pack b) :
    exactDigits t.items d = c.items := by
  rw [exactDigits_eq_convolution]
  apply PackedConvolution.certified hB
  · rw [overlap_outputLength]
    simpa only [Tree.length_items] using hn
  · intro k _
    rw [← event_eq_coeff]
    exact event_lt (fun _ hy => (Tree.le_high hy).trans hbox)
      (by simpa only [Tree.length_items] using hsize) k
  · exact fun x hx => ((Tree.le_high hx).trans hc).trans_lt hp
  · simpa only [Tree.pack_eq, Tree.other_eq] using hm

theorem all_events_le {t c : Tree} {b d p : ℕ} (hB : 1 < b)
    (hbox : t.high ≤ d) (hsize : t.size*t.size*d*d < b)
    (hc : c.high ≤ p) (hp : p < b) (hn : c.size = 2*t.size-1)
    (hm : t.pack b*t.other b d = c.pack b) (k : Fin (2*t.items.length-1)) :
    event t.items d k.val ≤ p := by
  have eq := digits_certified hB hbox hsize hc hp hn hm
  have mem : event t.items d k.val ∈ exactDigits t.items d := List.mem_ofFn.mpr ⟨k,rfl⟩
  exact (Tree.le_high (eq ▸ mem)).trans hc
end Overlap
