import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Overlap.Tree

set_option backward.isDefEq.respectTransparency false
namespace Overlap
open scoped BigOperators
namespace Tree

@[simp] theorem length_items (t : Tree) : t.items.length = t.size := by
  induction t with
  | leaf => simp [items, size]
  | node l r hl hr => simp [items, size, hl, hr]

@[simp] theorem sum_items (t : Tree) : t.items.sum = t.total := by
  induction t with
  | leaf => simp [items, total]
  | node l r hl hr => simp [items, total, hl, hr]

theorem le_high {t : Tree} {x : ℕ} (h : x ∈ t.items) : x ≤ t.high := by
  induction t with
  | leaf y => simpa [items,high] using (le_of_eq (List.mem_singleton.mp h))
  | node l r hl hr =>
    rcases List.mem_append.mp h with h | h
    · exact le_max_of_le_left (hl h)
    · exact le_max_of_le_right (hr h)

theorem pack_eq (t : Tree) (b : ℕ) : t.pack b = Nat.ofDigits b t.items := by
  induction t with
  | leaf x => simp [pack,items]
  | node l r hl hr => simp [pack,items,Nat.ofDigits_append,hl,hr]

theorem other_eq (t : Tree) (b d : ℕ) :
    t.other b d = Nat.ofDigits b ((t.items.map (d-·)).reverse) := by
  induction t with
  | leaf x => simp [other,items]
  | node l r hl hr => simp [other,items,Nat.ofDigits_append,hl,hr]

end Tree

theorem digits_sum (a : List ℕ) (b : ℕ) :
    Nat.ofDigits b a = ∑ i : Fin a.length, a[i.val] * b ^ i.val := by
  induction a with
  | nil => simp
  | cons x xs ih =>
    rw [Nat.ofDigits_cons, ih]
    conv_rhs => erw [Fin.sum_univ_succ]
    simp [pow_succ', Finset.mul_sum, Nat.mul_left_comm]

theorem reverse_sum (a : List ℕ) (b d : ℕ) :
    Nat.ofDigits b ((a.map (d-·)).reverse) =
      ∑ i : Fin a.length, (d-a[i.val])*b^(a.length-1-i.val) := by
  induction a with
  | nil => simp
  | cons x xs ih =>
    erw [Fin.sum_univ_succ]
    simp only [List.map_cons,List.reverse_cons,Nat.ofDigits_append,Nat.ofDigits_singleton,
      List.length_map,List.length_reverse,ih,List.length_cons,Fin.val_zero,Fin.val_succ,
      List.getElem_cons_zero,List.getElem_cons_succ,Nat.add_sub_cancel,Nat.sub_zero]
    rw [Nat.add_comm]
    congr 1
    · exact Nat.mul_comm _ _
    · apply Finset.sum_congr rfl
      intro i _
      congr 2; omega

def event (a : List ℕ) (d k : ℕ) : ℕ :=
  ∑ i : Fin a.length, ∑ j : Fin a.length,
    if i.val + (a.length-1-j.val) = k then a[i.val]*(d-a[j.val]) else 0

def exactDigits (a : List ℕ) (d : ℕ) : List ℕ :=
  List.ofFn fun k : Fin (2*a.length-1) => event a d k.val

theorem event_lt {a : List ℕ} {d b : ℕ} (ha : ∀ x ∈ a, x ≤ d)
    (hb : a.length*a.length*d*d < b) (k : ℕ) : event a d k < b := by
  have h : event a d k ≤ ∑ _i : Fin a.length, ∑ _j : Fin a.length, d*d := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact Nat.mul_le_mul (ha _ (List.getElem_mem _)) (Nat.sub_le _ _)
    · exact Nat.zero_le _
  simp at h
  exact lt_of_le_of_lt (by nlinarith only [h] : event a d k ≤ a.length*a.length*d*d) hb

theorem digits_ofFn_sum {n : ℕ} (f : Fin n → ℕ) (b : ℕ) :
    Nat.ofDigits b (List.ofFn f) = ∑ i : Fin n, f i * b^i.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons, ih, Fin.sum_univ_succ]
    simp [pow_succ', Finset.mul_sum, Nat.mul_left_comm]

theorem packed_events (a : List ℕ) (b d : ℕ) :
    Nat.ofDigits b (exactDigits a d) =
      Nat.ofDigits b a * Nat.ofDigits b ((a.map (d-·)).reverse) := by
  rw [exactDigits, digits_ofFn_sum, digits_sum a, reverse_sum]
  simp only [event]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  let v : Fin (2*a.length-1) := ⟨i.val+(a.length-1-j.val),by have := i.isLt; have := j.isLt; omega⟩
  calc
    _ = ∑ k : Fin (2*a.length-1), if v = k then
          (a[i.val]*(d-a[j.val]))*b^v.val else 0 := by
      apply Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin (2*a.length-1)))) rfl
      intro k _
      by_cases e : v = k
      · subst k; simp [v]
      · have ne : i.val+(a.length-1-j.val) ≠ k.val := fun h => e (Fin.ext h)
        simp [ne,e]
    _ = _ := by simp [v,pow_add]; ring

theorem digits_certified {t c : Tree} {b d p : ℕ} (hB : 1 < b)
    (hbox : t.high ≤ d) (hsize : t.size*t.size*d*d < b)
    (hc : c.high ≤ p) (hp : p < b) (hn : c.size = 2*t.size-1)
    (hm : t.pack b*t.other b d = c.pack b) :
    exactDigits t.items d = c.items := by
  apply Nat.ofDigits_inj_of_len_eq hB
  · simp [exactDigits,hn]
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact event_lt (fun y hy => (Tree.le_high hy).trans hbox) (by simpa using hsize) _
  · exact fun x hx => lt_of_le_of_lt ((Tree.le_high hx).trans hc) hp
  · simpa [packed_events, Tree.pack_eq, Tree.other_eq] using hm

theorem all_events_le {t c : Tree} {b d p : ℕ} (hB : 1 < b)
    (hbox : t.high ≤ d) (hsize : t.size*t.size*d*d < b)
    (hc : c.high ≤ p) (hp : p < b) (hn : c.size = 2*t.size-1)
    (hm : t.pack b*t.other b d = c.pack b) (k : Fin (2*t.items.length-1)) :
    event t.items d k.val ≤ p := by
  have eq := digits_certified hB hbox hsize hc hp hn hm
  have mem : event t.items d k.val ∈ exactDigits t.items d := List.mem_ofFn.mpr ⟨k,rfl⟩
  exact (Tree.le_high (eq ▸ mem)).trans hc
end Overlap
