/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth, Marc Masdeu
-/
import LftCM.Common
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Subtype
import Mathlib.GroupTheory.GroupAction.Prod
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Polyrith

set_option quotPrecheck false
noncomputable section

      linear_combination -(1 * hx) + x ^ 4 * h₀
    norm_num at this
  field_simp
  have h₁ : x - 1 ≠ 0 := by
    contrapose! hx'
    linear_combination hx'
  apply mul_left_cancel₀ h₁
  linear_combination x * hx

noncomputable def ϕ : ℝ → ℝ := fun x => (1 - x)⁻¹

example {x : ℝ} (h₁ : x ≠ 1) (h₀ : x ≠ 0) : ϕ (ϕ (ϕ x)) = x :=
  by
  dsimp [ϕ]
  have : 1 - x ≠ 0 := by contrapose! h₁ ; linear_combination -h₁
  have : -x ≠ 0 := by contrapose! h₀ ; linear_combination -h₀
  have : -x - (1 - x) ≠ 0 := by intro h; linarith
  field_simp
  ring


-- introduce notation for the circle
local notation "𝕊" => {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 1}

/-- Stereographic projection, forward direction. This is a map from `ℝ × ℝ` to `ℝ`. It is smooth
away from the horizontal line `p.2 = 1`.  It restricts on the unit circle to the stereographic
projection. -/
def stereoToFun (p : 𝕊) : ℝ :=
  2 * p.1.1 / (1 - p.1.2)

@[simp]
theorem stereoToFun_apply (p : 𝕊) : stereoToFun p = 2 * p.1.1 / (1 - p.1.2) := rfl

/-- Stereographic projection, reverse direction.  This is a map from `ℝ` to the unit circle `𝕊` in
`ℝ × ℝ`. -/
def stereoInvFun (w : ℝ) : 𝕊 :=
  ⟨(w ^ 2 + 4)⁻¹ • (4 * w, w ^ 2 - 4), by
    dsimp
    have : w ^ 2 + 4 ≠ 0 := by nlinarith
    field_simp
    ring⟩

@[simp]
theorem stereoInvFun_apply (w : ℝ) :
    (stereoInvFun w : ℝ × ℝ) = (w ^ 2 + 4)⁻¹ • (4 * w, w ^ 2 - 4) :=
  rfl


open Subtype

theorem stereoInvFun_ne_north_pole (w : ℝ) : stereoInvFun w ≠ (⟨(0, 1), by simp⟩ : 𝕊) := by
  dsimp
  rw [Subtype.ext_iff, Prod.mk.inj_iff]
  dsimp
  intro h
  have h₁ : w ^ 2 + 4 ≠ 0 := by nlinarith
  field_simp at h
  have : (8 : ℝ) = 0 := by linear_combination -h.2
  norm_num at this

theorem stereo_left_inv {p : 𝕊} (hp : (p : ℝ × ℝ) ≠ (0, 1)) : stereoInvFun (stereoToFun p) = p := by
  ext1
  obtain ⟨⟨x, y⟩, pythag⟩ := p
  dsimp at pythag hp ⊢
  rw [Prod.mk.inj_iff] at hp ⊢
  have ha : 1 - y ≠ 0
  · contrapose! hp with ha
    have : y = 1 := by linear_combination -ha
    refine' ⟨_, this⟩
    have : x ^ 2 = 0 := by linear_combination pythag - (y + 1) * this
    exact pow_eq_zero this
  constructor
  · field_simp
    linear_combination 4 * (y - 1) * x * pythag
  · field_simp
    linear_combination -4 * (y - 1) ^ 3 * pythag

theorem stereo_right_inv (w : ℝ) : stereoToFun (stereoInvFun w) = w := by
  dsimp
  have : w ^ 2 + 4 ≠ 0 := by nlinarith
  field_simp
  ring

example {i j : ℕ} :
    ((i + 1).centralBinom : ℚ) * j.centralBinom * (i - j + 1) / (2 * (i + j + 1) * (i + j + 2)) -
        i.centralBinom * (j + 1).centralBinom * (i - j - 1) / (2 * (i + j + 1) * (i + j + 2)) =
      i.centralBinom / (i + 1) * (j.centralBinom / (j + 1)) := by
  have h₁ : ((i : ℚ) + 1) * (i + 1).centralBinom = 2 * (2 * i + 1) * i.centralBinom
  · exact_mod_cast i.succ_mul_centralBinom_succ
  -- BOTH:
  have h₂ : ((j : ℚ) + 1) * (j + 1).centralBinom = 2 * (2 * j + 1) * j.centralBinom
  · exact_mod_cast j.succ_mul_centralBinom_succ
  -- BOTH:
  have : (i : ℚ) + j + 1 ≠ 0
  · norm_cast
    exact (i+j).succ_ne_zero
  -- BOTH:
  have : (i : ℚ) + j + 2 ≠ 0
  · norm_cast
    exact Nat.succ_ne_zero (i + j + 1)
  -- BOTH:
  have : (i : ℚ) + 1 ≠ 0
  · norm_cast
    exact Nat.succ_ne_zero i
  -- BOTH:
  have : (j : ℚ) + 1 ≠ 0
  · norm_cast
    exact Nat.succ_ne_zero j
  field_simp
  generalize ((Nat.centralBinom i) : ℚ) = Bi at *
  generalize ((Nat.centralBinom j) : ℚ) = Bj at *
  generalize ((Nat.centralBinom (i+1)) : ℚ) = Bii at *
  generalize ((Nat.centralBinom (j+1)) : ℚ) = Bjj at *
  generalize (i : ℚ) = ii at *
  generalize (j : ℚ) = jj at *
  linear_combination
    (-(1 * Bj * jj ^ 2) + 1 / 4 * ii * jj * Bjj + 1 / 2 * Bj * ii + Bj * jj + 1 / 4 * ii * Bjj - 1 / 4 * jj * Bjj +
            3 / 2 * Bj -
          1 / 4 * Bjj) *
        h₁ +
      (-(1 / 4 * Bii * ii ^ 2) + ii * jj * Bi - 1 / 2 * ii * Bi + jj * Bi + 1 / 4 * Bii + 1 / 2 * Bi) * h₂
