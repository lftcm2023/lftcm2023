import Mathlib

open Real

-- # Intro
-- Lean is a dependently-typed language

-- Every expression has a type, and `#check` can tell you the type

#check 2
#check 17 + 4
#check π
#check rexp 1

-- Types are expressions too!

#check ℕ
#check ℝ

-- We can also make our own expressions, and give them names
def myFavouriteNumber : ℕ := 7

def yourFavouriteNumber : ℕ := sorry
-- sorry works as a placeholder

#check myFavouriteNumber

-- or not give them a name
example : ℕ := 2

-- # But this isn't maths!

-- The type `Prop` contains `Prop`ositions...

#check 2 + 2 = 4
#check rexp 1 < π

-- ...including false propositions...
#check 2 + 2 = 5
-- ...and open questions
#check Irrational (rexp 1 + π)
#check myFavouriteNumber = yourFavouriteNumber

def MyDifficultProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)
def MyEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)
def MyVeryEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p

-- Key! If `p : Prop`, an expression of type `p` is a proof of `p`.

example : 2 + 2 = 4 := rfl
example : 2 + 2 ≠ 5 := by simp
example : ∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 4 * x * y * z = n * (x * y + x * z + y * z) := sorry
-- Erdős-Strauss conjecture

example (n : ℕ) (hn : 2 ≤ n) :
  ∃ x y z : ℕ, 4 * x * y * z = n * (x * y + x * z + y * z) := sorry

-- # How can we make these expressions?

-- Simple proof terms
example : True := trivial
example : 2 = 2 := rfl
example (a b : ℕ) : a + b = b + a := Nat.add_comm a b

example (a b : ℕ) : a * b = b * a := Nat.mul_comm a b

theorem my_proof : MyVeryEasyProposition := fun n => ⟨n, le_rfl⟩

#check MyVeryEasyProposition
#check my_proof
-- my proposition "has type Proposition", or "is a proposition"
-- my proof "has type my proposition", or "has type ∀ n : ℕ, ∃ p, n ≤ p",
--    or "is a proof of ∀ n : ℕ, ∃ p, n ≤ p"

-- But just proof terms get ugly...
example (a b : ℕ) : a + a * b = (b + 1) * a :=
  (add_comm a (a * b)).trans ((mul_add_one a b).symm.trans (mul_comm a (b + 1)))



-- Very clever tactics
example (a b : ℕ) : a + a * b = (b + 1) * a := by ring

example : 2 + 2 ≠ 5 := by simp
example : 4 ^ 25 < 3 ^ 39 := by norm_num

open Nat

-- Simple tactics
example (a b : ℕ) : a + b = b + a := by exact Nat.add_comm a b
example : 3 = 3 := by rfl

#check add_mul (R := ℕ)

-- In practice we write tactic proofs, and write them with help of the infoview
example (a b : ℕ) : a + a * b = (b + 1) * a := by
  rw [add_mul b 1 a, one_mul a, add_comm a (a * b), mul_comm a b]
  --> S01_Calculating.lean has many examples and some more information about using `rw`

theorem Euclid_Thm (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  let p := minFac (Nat.factorial n + 1)
  have f1 : factorial n + 1 ≠ 1 := Nat.ne_of_gt <| Nat.succ_lt_succ <| factorial_pos _
  have pp : Nat.Prime p := minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ factorial n := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  exact ⟨p, np, pp⟩

theorem Ugly_Euclid_Thm (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p :=
  have pp := minFac_prime (add_left_ne_self.2 (factorial_pos n).ne')
  ⟨_, le_of_not_le fun h => pp.not_dvd_one ((Nat.dvd_add_iff_right (dvd_factorial pp.pos h)).2
    (minFac_dvd _)), pp⟩

-- The proof doesn't matter
example : Euclid_Thm = Ugly_Euclid_Thm := rfl
-- *to Lean*

  --> S02_Overview.lean has more examples of tactic proofs

-- Some tactics can self-replace
theorem Easy_Euclid_Thm (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by exact?

example (a b : ℕ) : a + a * b = (b + 1) * a := by
  rw?
  sorry

-- # Some more difficult proofs
def myFactorial : ℕ → ℕ
| 0 => 1
| (n + 1) => (n + 1) * myFactorial n

#check (myFactorial : ℕ → ℕ)

-- Lean can compute too!
#eval myFactorial 10
-- sometimes useful for sanity-checking definitions

theorem myFactorial_add_one (n : ℕ) : myFactorial (n + 1) = (n + 1) * myFactorial n := rfl
theorem myFactorial_zero : myFactorial 0 = 1 := rfl

theorem myFactorial_pos (n : ℕ) : 0 < myFactorial n := by
  induction' n with n ih
  · rw [myFactorial_zero]
    simp
  · rw [succ_eq_add_one, myFactorial_add_one]
    apply mul_pos
    · exact succ_pos n
    · exact ih

theorem myFactorial_pos' (n : ℕ) : 0 < myFactorial n := by
  induction n
  case zero =>
    rw [myFactorial_zero]
    simp
  case succ n ih =>
    rw [succ_eq_add_one, myFactorial_add_one]
    apply mul_pos
    · exact succ_pos n
    · exact ih

-- # Personal note: this scales!
open BigOperators

def upper_density (A : Set ℕ) : ℝ := sorry

-- first posed: Erdős-Graham <1980?
-- partial progress annals, 2003
-- arXiv: Bloom, Dec 2021
-- quanta: Jan 2022
-- Lean: Bloom - M., Jun 2022, 12k lines
theorem bloom (A : Set ℕ) (hA : 0 < upper_density A) :
  ∃ B : Finset ℕ, ↑B ⊆ A ∧ ∑ i in B, (1 / i : ℚ) = 1 := sorry

def diagonal_ramsey (k : ℕ) : ℕ := sorry

-- first posed: Erdős <1935?
-- partial progress annals: 2009
-- arXiv: Mar 2023
-- quanta: Apr 2023
-- Lean: M., within this month? 14k+
theorem campos_griffiths_morris_sahasrabudhe :
  ∃ c : ℝ, 0 < c ∧ ∀ k, diagonal_ramsey k ≤ (4 - c) ^ k := sorry

-- Expressions and types, every expression has a type
-- A proof has type given by what it's proved!

-- Useful tactics:
  -- rw
  -- exact
  -- apply
  -- simp
  -- induction

  -- ring, norm_num, positivity, linarith
  -- refine

-- More examples in S03, S04, S05, S06
--  curly braces
--  calc


-- # Footnotes

-- ## Dependently typed
#check Fin 10
#check Fin

example (n : ℕ) : Fintype.card (Fin n) = n := by simp

-- ## terminal simps
example (n : ℕ) : Fintype.card (Fin n) = n := by simp?

-- ## naming
-- https://leanprover-community.github.io/contribute/naming.html

-- ## hierarchy!
#check 3
#check 4 = 4
#check ℕ
#check Prop
#check Type
#check Type 1
#check Type 2

#check Type 0

-- myproof : myVeryEasyProposition : Prop : Type : Type 1 : Type 2 : Type 3 : ...
