/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth, Marc Masdeu
-/
import LftCM.Common
import Mathlib.Data.MvPolynomial.PDeriv
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Tactic.Polyrith
import LftCM.Attr


example {x : ℚ} (hx : x ^ 2 - 4 * x = - 4) : x = 2 := by
  polyrith

example {x : ℤ} (hx : x ^ 2 - 4 * x = -4) : x = 2 := by
  have : (x - 2) ^ 2 = 0 := by
    polyrith
  polyrith

example {r s : ℚ} (hr : r ≠ 1) (h : r * s - 2 = s - 2 * r) : s = -2 := by
  have hr' : r - 1 ≠ 0
  · contrapose! hr
    polyrith
  polyrith

example {r s : ℚ} (h : r * s - 2 = s - 2 * r) : True := by
  have : (r - 1) * (s + 2) = 0 := by
    polyrith
-- use (2x+1), (1-x+√3y), (1-x-√3y) for a nice picture
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
  sorry
end klein

section weierstrass

-- NB cubic depicted is y ^ 2 = x ^ 3 - x + 1
variable (p q : K)

/-- Defining polynomial for a Weierstrass-form elliptic curve zy² = x³ + pxz² + qz³ as a projective
hypersurface in Kℙ². -/
@[reducible]
def weierstrass : MvPolynomial (Fin 3) K :=
  -X 2 * X 1 ^ 2 + X 0 ^ 3 + C p * X 0 * X 2 ^ 2 + C q * X 2 ^ 3


set_option maxHeartbeats 500000

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
  sorry

end weierstrass
