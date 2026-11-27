import Mathlib.Tactic

namespace Overlap

/-- A fractional assignment of finitely many Boolean coordinates. -/
def InCube {ι : Type*} (x : ι → ℝ) : Prop := ∀ i, x i ∈ Set.Icc 0 1

private def potential (t x : ℝ) : ℝ := x^4 + 32*t*x^2

private theorem potential_step {x d t : ℝ} (ht : 0 ≤ t) (hd : |d| ≤ 2) :
    potential t (x+d) ≤ potential (t+1) x + (4*x^3+64*t*x)*d + (48+128*t) := by
  obtain ⟨hl,hr⟩ := abs_le.mp hd
  have h₂ : 0 ≤ 4-d^2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 2-d) (by linarith : 0 ≤ 2+d)]
  unfold potential
  nlinarith only [sq_nonneg (x*d-d^2), mul_nonneg (sq_nonneg x) h₂,
    mul_nonneg h₂ (by positivity : 0 ≤ 4+d^2), mul_nonneg ht h₂]

private theorem potential_split {a b x p t : ℝ} (hp : p ∈ Set.Icc 0 1)
    (ht : 0 ≤ t) (he : x = (1-p)*a + p*b) (hd : |b-a| ≤ 2) :
    (1-p)*potential t a + p*potential t b ≤ potential (t+1) x + (48+128*t) := by
  have da : a-x = -p*(b-a) := by rw [he]; ring
  have db : b-x = (1-p)*(b-a) := by rw [he]; ring
  have sa : |a-x| ≤ 2 := by
    rw [da, abs_mul, abs_neg, abs_of_nonneg hp.1]
    calc
      p*|b-a| ≤ 1*2 := mul_le_mul hp.2 hd (abs_nonneg _) zero_le_one
      _ = _ := by ring
  have sb : |b-x| ≤ 2 := by
    rw [db, abs_mul, abs_of_nonneg (sub_nonneg.mpr hp.2)]
    exact (mul_le_mul (show 1-p ≤ 1 by linarith [hp.1]) hd (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have la := potential_step (x := x) ht sa
  have lb := potential_step (x := x) ht sb
  rw [show x+(a-x)=a by ring] at la
  rw [show x+(b-x)=b by ring] at lb
  have centered : (1-p)*(a-x)+p*(b-x)=0 := by rw [da,db]; ring
  nlinarith only [mul_le_mul_of_nonneg_left la (sub_nonneg.mpr hp.2),
    mul_le_mul_of_nonneg_left lb hp.1, congrArg (fun z : ℝ => (4*x^3+64*t*x)*z) centered]

/-- Simultaneous rounding of multi-affine observables with coordinate oscillation at most two.
The fourth-power bound is uniform over the finite family. -/
theorem round_cube_fourth {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (p : ι → ℝ) (hp : InCube p) (F : κ → (ι → ℝ) → ℝ)
    (ha : ∀ x, InCube x → ∀ i j, F j x =
      (1-x i)*F j (Function.update x i 0) + x i*F j (Function.update x i 1))
    (hd : ∀ x, InCube x → ∀ i j,
      |F j (Function.update x i 1) - F j (Function.update x i 0)| ≤ 2) :
    ∃ q : ι → ℝ, (∀ i, q i = 0 ∨ q i = 1) ∧
      ∀ j, (F j q - F j p)^4 ≤ (Fintype.card κ : ℝ) *
        (128*(Fintype.card ι : ℝ)^2 + 48*(Fintype.card ι : ℝ)) := by
  classical
  let V (t : ℝ) (x : ι → ℝ) := ∑ j, potential t (F j x - F j p)
  let R (t : ℝ) := (Fintype.card κ : ℝ) * (128*t^2 + 48*t)
  have aux (s : Finset ι) (x : ι → ℝ) (hx : InCube x) :
      ∃ q, (∀ i ∈ s, q i = 0 ∨ q i = 1) ∧ (∀ i ∉ s, q i = x i) ∧
        V 0 q ≤ V s.card x + R s.card := by
    induction s using Finset.induction_on generalizing x with
    | empty => exact ⟨x, by simp, by simp, by simp [R]⟩
    | @insert i s hi ih =>
      let x₀ := Function.update x i 0
      let x₁ := Function.update x i 1
      have keep (b : ℝ) (hb : b ∈ Set.Icc (0:ℝ) 1) :
          InCube (Function.update x i b) := by
        intro l
        by_cases h : l=i
        · simpa [h] using hb
        · simpa [Function.update_of_ne h] using hx l
      let t : ℝ := s.card
      let C : ℝ := (Fintype.card κ : ℝ) * (48+128*t)
      have split : (1-x i)*V t x₀ + x i*V t x₁ ≤ V (t+1) x + C := by
        unfold V C
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        calc
          _ ≤ ∑ j : κ, (potential (t+1) (F j x - F j p) + (48+128*t)) := by
            apply Finset.sum_le_sum
            intro j _
            apply potential_split (hx i) (by dsimp [t]; positivity)
            · dsimp [x₀,x₁]; rw [ha x hx i j]; ring
            · dsimp [x₀,x₁]; simpa only [sub_sub_sub_cancel_right] using hd x hx i j
          _ = _ := by simp [Finset.sum_add_distrib, mul_add]
      have branch : V t x₀ ≤ V (t+1) x + C ∨ V t x₁ ≤ V (t+1) x + C := by
        by_contra! h
        have hl := mul_le_mul_of_nonneg_left h.1.le (sub_nonneg.mpr (hx i).2)
        by_cases hz : x i = 0
        · simp [hz] at split
          linarith
        · have hr := mul_lt_mul_of_pos_left h.2 (lt_of_le_of_ne (hx i).1 (Ne.symm hz))
          linarith
      obtain ⟨b, hb, hV⟩ : ∃ b : ℝ, (b=0 ∨ b=1) ∧
          V t (Function.update x i b) ≤ V (t+1) x + C := by
        rcases branch with h | h
        · exact ⟨0, Or.inl rfl, h⟩
        · exact ⟨1, Or.inr rfl, h⟩
      obtain ⟨q,hbit,hsame,hq⟩ := ih (Function.update x i b) (keep b (by rcases hb with rfl|rfl <;> constructor <;> norm_num))
      refine ⟨q, ?_, ?_, ?_⟩
      · intro l hl
        rcases Finset.mem_insert.mp hl with he | h
        · subst l
          rw [hsame i hi, Function.update_self]
          exact hb
        · exact hbit l h
      · intro l hl
        have hs : l ∉ s := fun h => hl (Finset.mem_insert_of_mem h)
        have hne : l ≠ i := fun h => hl (Finset.mem_insert.mpr (Or.inl h))
        rw [hsame l hs, Function.update_of_ne hne]
      · rw [Finset.card_insert_of_notMem hi, Nat.cast_add_one]
        change V 0 q ≤ V (t+1) x + R (t+1)
        have hR : C + R t ≤ R (t+1) := by
          dsimp [C,R]
          have ht : 0 ≤ t := by dsimp [t]; positivity
          nlinarith only [mul_nonneg (Nat.cast_nonneg (Fintype.card κ) : (0:ℝ) ≤ _) (show 0 ≤ 128*t+128 by linarith)]
        linarith
  obtain ⟨q,hq,_,bound⟩ := aux Finset.univ p hp
  refine ⟨q, fun i => hq i (Finset.mem_univ _), fun j => ?_⟩
  have h := Finset.single_le_sum (f := fun j => (F j q-F j p)^4)
    (fun j _ => by positivity) (Finset.mem_univ j)
  exact h.trans (by simpa [V,R,potential] using bound)
#print axioms round_cube_fourth
end Overlap
