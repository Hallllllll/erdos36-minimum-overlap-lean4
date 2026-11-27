import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Overlap.Tree

/-! Carry-free packing for ordinary convolution of two lists of natural numbers. -/

set_option backward.isDefEq.respectTransparency false
namespace Overlap
open scoped BigOperators
namespace Tree

@[simp] theorem length_items (t : Tree) : t.items.length = t.size := by
  induction t with
  | leaf => simp [items, size]
  | node l r hl hr => simp [items, size, hl, hr]

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

end Tree

theorem digits_sum (a : List ℕ) (b : ℕ) :
    Nat.ofDigits b a = ∑ i : Fin a.length, a[i.val] * b ^ i.val := by
  induction a with
  | nil => simp
  | cons x xs ih =>
    rw [Nat.ofDigits_cons, ih]
    conv_rhs => erw [Fin.sum_univ_succ]
    simp [pow_succ', Finset.mul_sum, Nat.mul_left_comm]

theorem digits_ofFn_sum {n : ℕ} (f : Fin n → ℕ) (b : ℕ) :
    Nat.ofDigits b (List.ofFn f) = ∑ i : Fin n, f i * b^i.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons, ih, Fin.sum_univ_succ]
    simp [pow_succ', Finset.mul_sum, Nat.mul_left_comm]

namespace PackedConvolution

/-- Length of the fixed-width convolution, including any high zero coefficients.
An empty operand gives the empty convolution. -/
def outputLength (m n : ℕ) : ℕ :=
  if m = 0 ∨ n = 0 then 0 else m + n - 1

private theorem add_lt_outputLength {m n : ℕ} (i : Fin m) (j : Fin n) :
    i.val + j.val < outputLength m n := by
  have hi := i.isLt
  have hj := j.isLt
  rw [outputLength, ite_eq_right (by omega)]
  omega

/-- The coefficient of degree `k` in the ordinary product of two coefficient lists. -/
def coeff (xs ys : List ℕ) (k : ℕ) : ℕ :=
  ∑ i : Fin xs.length, ∑ j : Fin ys.length,
    if i.val + j.val = k then xs[i.val] * ys[j.val] else 0

/-- The convolution in increasing degree order. -/
def convolution (xs ys : List ℕ) : List ℕ :=
  List.ofFn fun k : Fin (outputLength xs.length ys.length) => coeff xs ys k.val

@[simp] theorem length_convolution (xs ys : List ℕ) :
    (convolution xs ys).length = outputLength xs.length ys.length :=
  List.length_ofFn

/-- A sufficient bound obtained by bounding every pair in the rectangular sum. -/
theorem coeff_lt {xs ys : List ℕ} {xMax yMax base : ℕ}
    (hx : ∀ x ∈ xs, x ≤ xMax) (hy : ∀ y ∈ ys, y ≤ yMax)
    (hbase : xs.length * ys.length * xMax * yMax < base) (k : ℕ) :
    coeff xs ys k < base := by
  have bound : coeff xs ys k ≤ ∑ _i : Fin xs.length, ∑ _j : Fin ys.length, xMax * yMax := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact Nat.mul_le_mul (hx _ (List.getElem_mem _)) (hy _ (List.getElem_mem _))
    · exact Nat.zero_le _
  exact lt_of_le_of_lt (by simpa [Nat.mul_assoc] using bound) hbase

/-- Packing commutes with convolution for every evaluation base.
Digit bounds are only needed to recover coefficients from the packed value. -/
theorem packed (xs ys : List ℕ) (base : ℕ) :
    Nat.ofDigits base (convolution xs ys) = Nat.ofDigits base xs * Nat.ofDigits base ys := by
  rw [convolution, digits_ofFn_sum, digits_sum xs, digits_sum ys]
  simp only [coeff]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  let degree : Fin (outputLength xs.length ys.length) :=
    ⟨i.val + j.val, add_lt_outputLength i j⟩
  calc
    _ = ∑ k : Fin (outputLength xs.length ys.length),
        if degree = k then (xs[i.val] * ys[j.val]) * base ^ degree.val else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : degree = k
      · subst k
        simp [degree]
      · have hne : i.val + j.val ≠ k.val := fun he => h (Fin.ext he)
        simp [hne, h]
    _ = _ := by simp [degree, pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Soundness of a fixed-length packed certificate with carry-free coefficients. -/
theorem certified {xs ys proposed : List ℕ} {base : ℕ} (hbase : 1 < base)
    (hlen : proposed.length = outputLength xs.length ys.length)
    (hcoeff : ∀ k < outputLength xs.length ys.length, coeff xs ys k < base)
    (hproposed : ∀ c ∈ proposed, c < base)
    (hmul : Nat.ofDigits base xs * Nat.ofDigits base ys = Nat.ofDigits base proposed) :
    convolution xs ys = proposed := by
  apply Nat.ofDigits_inj_of_len_eq hbase
  · simpa only [length_convolution] using hlen.symm
  · intro c hc
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hc
    exact hcoeff k.val k.isLt
  · exact hproposed
  · exact (packed xs ys base).trans hmul

/-- Tree certificates use the same convolution and check packing, length and digit bounds
through the tree operations. -/
theorem tree_certified {xs ys proposed : Tree} {base : ℕ} (hbase : 1 < base)
    (hlen : proposed.size = outputLength xs.size ys.size)
    (hbound : xs.size * ys.size * xs.high * ys.high < base)
    (hproposed : proposed.high < base)
    (hmul : xs.pack base * ys.pack base = proposed.pack base) :
    convolution xs.items ys.items = proposed.items := by
  apply certified hbase
  · simpa only [Tree.length_items] using hlen
  · intro k _
    exact coeff_lt (fun _ hx => Tree.le_high hx) (fun _ hy => Tree.le_high hy)
      (by simpa only [Tree.length_items] using hbound) k
  · exact fun c hc => (Tree.le_high hc).trans_lt hproposed
  · simpa only [Tree.pack_eq] using hmul

end PackedConvolution
end Overlap
