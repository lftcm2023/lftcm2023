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


example (a b : ℚ) (ha : a ≠ 0) (H : b = a ^ 2 + 3 * a) : b / a - a = 3 := by
  field_simp
  linear_combination H

example (m n : ℝ) (hmn : (m, n) ≠ 0) :
    ((m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2)) ^ 2 + (2 * m * n / (m ^ 2 + n ^ 2)) ^ 2 = 1 :=
  by
  have : m ^ 2 + n ^ 2 ≠ 0 := by
    contrapose! hmn
    have hm : m = 0 := by nlinarith
    have hn : n = 0 := by nlinarith
    simp [hm, hn]
  field_simp
  ring

example {x : ℂ} (hx : x ^ 5 = 1) (hx' : x ≠ 1) : (x + 1 / x) ^ 2 + (x + 1 / x) - 1 = 0 :=
  by
  have : x ≠ 0 := by
    intro h₀
    have : (1 : ℂ) = 0 := by
      polyrith
    polyrith
  polyrith
noncomputable def ϕ : ℝ → ℝ := fun x => (1 - x)⁻¹

example {x : ℝ} (h₁ : x ≠ 1) (h₀ : x ≠ 0) : ϕ (ϕ (ϕ x)) = x :=
  by
  dsimp [ϕ]
    sorry


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
    sorry
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
  sorry

theorem stereo_left_inv {p : 𝕊} (hp : (p : ℝ × ℝ) ≠ (0, 1)) : stereoInvFun (stereoToFun p) = p := by
  ext1
  obtain ⟨⟨x, y⟩, pythag⟩ := p
  dsimp at pythag hp ⊢
  rw [Prod.mk.inj_iff] at hp ⊢
  sorry

theorem stereo_right_inv (w : ℝ) : stereoToFun (stereoInvFun w) = w := by
  dsimp
  sorry

/-- Stereographic projection, as a bijection to `ℝ` from the complement of `(0, 1)` in the unit
circle `𝕊` in `ℝ × ℝ`. -/
def stereographicProjection : ({(⟨(0, 1), by simp⟩ : 𝕊)}ᶜ : Set 𝕊) ≃ ℝ
    where
  toFun := stereoToFun ∘ (·)
  invFun w := ⟨stereoInvFun w, stereoInvFun_ne_north_pole w⟩
  left_inv p := by
    apply Subtype.ext
    apply stereo_left_inv
    simpa [Subtype.ext_iff] using p.prop
  right_inv w := stereo_right_inv w


#check Nat.centralBinom
-- nat.central_binom : ℕ → ℕ

#check Nat.succ_mul_centralBinom_succ

#check Nat.succ_ne_zero

-- nat.succ_ne_zero : ∀ (n : ℕ), n.succ ≠ 0

example {i j : ℕ} :
    ((i + 1).centralBinom : ℚ) * j.centralBinom * (i - j + 1) / (2 * (i + j + 1) * (i + j + 2)) -
        i.centralBinom * (j + 1).centralBinom * (i - j - 1) / (2 * (i + j + 1) * (i + j + 2)) =
      i.centralBinom / (i + 1) * (j.centralBinom / (j + 1)) := by
  have h₁ : ((i : ℚ) + 1) * (i + 1).centralBinom = 2 * (2 * i + 1) * i.centralBinom
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  sorry
