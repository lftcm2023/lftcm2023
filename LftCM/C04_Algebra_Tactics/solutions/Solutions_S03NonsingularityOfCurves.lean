/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth, Marc Masdeu
-/
import LftCM.Common
import Mathlib.Data.MvPolynomial.PDeriv
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Tactic.Polyrith
import LftCM.Attr

  sorry
-- polyrith failed to retrieve a solution from Sage! ValueError: polynomial is not in the ideal

    linear_combination hx
  have := pow_eq_zero this
  linear_combination this

    linear_combination hr
  apply mul_left_cancel₀ hr'
  linear_combination h

    linear_combination h
  cases' eq_zero_or_eq_zero_of_mul_eq_zero this with H H
  -- the case `r - 1 = 0`
  · exact trivial
  -- the case `s + 2 = 0`
  · exact trivial

noncomputable section

open MvPolynomial

variable (K : Type _) [Field K] [CharZero K]

/-! This file contains a lot of computationally-intensive evaluation of polynomials and their
derivatives. We speed it up slightly by specifiying in advance the path the simplifier should take.
-/


-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'

attribute [polynomial_simps] MvPolynomial.eval_X MvPolynomial.eval_C
  map_add map_sub map_mul map_neg map_bit0 map_bit1 map_one map_pow map_zero
  Matrix.cons_val_zero Matrix.cons_val_one Matrix.head_cons
  Matrix.cons_vec_bit0_eq_alt0 Matrix.cons_vec_bit1_eq_alt1
  Matrix.cons_vecAlt0 Matrix.cons_vecAlt1
  Matrix.cons_vecAppend Matrix.empty_vecAppend
  Derivation.leibniz Derivation.leibniz_pow pderiv_C pderiv_X_of_ne pderiv_X_self Pi.single_eq_of_ne
  Algebra.id.smul_eq_mul nsmul_eq_mul
  Nat.cast_bit1 Nat.cast_bit0 Nat.cast_one
  -- `ring`/`linear_combination` would take care of the next ones, but we add them to aid human
  -- inspection
  mul_zero zero_mul mul_one one_mul add_zero zero_add pow_one mul_neg neg_zero

section klein

/-- Defining polynomial for the Klein quartic curve x³y + y³z + z³x = 0 as a projective hypersurface
in Kℙ². -/
@[reducible]
def klein : MvPolynomial (Fin 3) K :=
  X 0 ^ 3 * X 1 + X 1 ^ 3 * X 2 + X 2 ^ 3 * X 0

/-- The Klein quartic is nonsingular. -/
example {x y z : K} (h : MvPolynomial.eval ![x, y, z] (klein K) = 0)
    (hdz : ∀ i, MvPolynomial.eval ![x, y, z] (MvPolynomial.pderiv i (klein K)) = 0) :
    ![x, y, z] = 0 := by
  have : 3 - 1 = 2 := by norm_num
  have h₀ := hdz 0
  have h₁ := hdz 1
  have h₂ := hdz 2
  simp only [this, polynomial_simps] at h h₀ h₁ h₂
  norm_num at h h₀ h₁ h₂
  have : y ^ 3 * z = 0
  · linear_combination -1 * h / 21 - 2 / 21 * x * h₀ + y * h₁ / 3 + z * h₂ / 21
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with hy | rfl
  · replace hy := pow_eq_zero hy
    subst hy
    have hz : z ^ 3 = 0
    · linear_combination h₀
    have hx : x ^ 3 = 0
    · linear_combination h₁
    replace hz := pow_eq_zero hz
    replace hx := pow_eq_zero hx
    simp [hx, hz]
  · have hx : x ^ 3 = 0
    · linear_combination h₁
    have hy : y ^ 3 = 0
    · linear_combination h₂
    replace hx := pow_eq_zero hx
    replace hy := pow_eq_zero hy
    simp [hx, hy]
end klein

section weierstrass

variable (p q : K)

/-- Defining polynomial for a Weierstrass-form elliptic curve zy² = x³ + pxz² + qz³ as a projective
hypersurface in Kℙ². -/
@[reducible]
def weierstrass : MvPolynomial (Fin 3) K :=
  -X 2 * X 1 ^ 2 + X 0 ^ 3 + C p * X 0 * X 2 ^ 2 + C q * X 2 ^ 3

/-- A Weierstrass-form elliptic curve with nonzero discriminant `27 * q ^ 2 + 4 * p ^ 3` is
nonsingular. -/
example {x y z : K} (disc : 27 * q ^ 2 + 4 * p ^ 3 ≠ 0)
    (h : MvPolynomial.eval ![x, y, z] (weierstrass K p q) = 0)
    (hdz : ∀ i, MvPolynomial.eval ![x, y, z] (MvPolynomial.pderiv i (weierstrass K p q)) = 0) :
    ![x, y, z] = 0 := by
  have h₀ := hdz 0
  have h₁ := hdz 1
  have h₂ := hdz 2
  simp at h h₀ h₁ h₂
  norm_num at h h₀ h₁ h₂
  -- deal separately with the line at infinity, `z = 0`
  rcases eq_or_ne z 0 with rfl | hz
  · have hx : x ^ 2 = 0
    · linear_combination h₀ / 3
    have hy : y ^ 2 = 0
    · linear_combination -(1 * h₂)
    replace hx := pow_eq_zero hx
    replace hy := pow_eq_zero hy
    simp [hx, hy]
  -- otherwise we'll deduce the discriminant must be zero
  · apply absurd (h₂ := disc)
    have hy : y = 0 := by tauto
    have H₁ : 2 * p * x + 3 * q * z = 0
    · apply mul_left_cancel₀ hz
      linear_combination h₂ + y * hy
    have H₂ : 9 * q * x - 2 * p ^ 2 * z = 0
    · apply mul_left_cancel₀ hz
      linear_combination -(2 * p * h₀) + 3 * x * H₁
    apply mul_left_cancel₀ hz
    linear_combination 9 * q * H₁ - 2 * p * H₂

end weierstrass
