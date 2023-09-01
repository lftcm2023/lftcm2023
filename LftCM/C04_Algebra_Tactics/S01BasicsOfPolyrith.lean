/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import LftCM.Common
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Polyrith

example {a b : ℂ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 :=
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * b := by rw [h₁]
    _ = -6 + 5 * (b + 2) := by ring
    _ = -6 + 5 * 3 := by rw [h₂]
    _ = 9 := by ring


example {a b : ℝ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 := by linarith


example {a b : ℂ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 := by linear_combination h₁ + 5 * h₂


example {m n : ℤ} (h : m - n = 0) : m = n := by linear_combination h


example {K : Type _} [Field K] [CharZero K] {s : K} (hs : 3 * s + 1 = 4) : s = 1 := by
  linear_combination 1 / 3 * hs


example {p q : ℂ} (h₁ : p + 2 * q = 4) (h₂ : p - 2 * q = 2) : 2 * p = 6 := by
  linear_combination h₁ + h₂


example {x y : ℤ} (h₁ : 2 * x + y = 4) (h₂ : x + y = 1) : x = 3 := by
  sorry
example {r s : ℝ} (h₁ : r + 2 * s = -1) (h₂ : s = 3) : r = -7 := by
  sorry
example {c : ℚ} (h₁ : 4 * c + 1 = 3 * c - 2) : c = -3 := by
  sorry
example {x y : ℤ} (h₁ : x - 3 * y = 5) (h₂ : y = 3) : x = 14 := by
  sorry
example {x y : ℤ} (h₁ : 2 * x - y = 4) (h₂ : y - x + 1 = 2) : x = 5 := by
  sorry
example {x y : ℝ} (h₁ : x = 3) (h₂ : y = 4 * x - 3) : y = 9 := by
  sorry
example {a b c : ℝ} (h₁ : a + 2 * b + 3 * c = 7) (h₂ : b + 2 * c = 3) (h₃ : c = 1) : a = 2 := by
  sorry
example {a b : ℝ} (h₁ : a + 2 * b = 4) (h₂ : a - b = 1) : a = 2 := by
  sorry
example {u v : ℚ} (h₁ : u + 2 * v = 4) (h₂ : u - 2 * v = 6) : u = 5 := by
  sorry
example {u v : ℚ} (h₁ : 4 * u + v = 3) (h₂ : v = 2) : u = 1 / 4 := by
  sorry

example {x y z w : ℂ} (h₁ : x * z = y ^ 2) (h₂ : y * w = z ^ 2) : z * (x * w - y * z) = 0 := by
  linear_combination w * h₁ + y * h₂


example {a b : ℚ} (h : a = b) : a ^ 2 = b ^ 2 := by linear_combination (a + b) * h


example {a b : ℚ} (h : a = b) : a ^ 3 = b ^ 3 := by linear_combination (a ^ 2 + a * b + b ^ 2) * h


example (m n : ℤ) : (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  linear_combination


example {x y : ℝ} (h₁ : x + 3 = 5) (h₂ : 2 * x - y * x = 0) : y = 2 := by
  sorry
example {x y : ℝ} (h₁ : x - y = 4) (h₂ : x * y = 1) : (x + y) ^ 2 = 20 := by
  sorry
example {a b c d e f : ℤ} (h₁ : a * d = b * c) (h₂ : c * f = d * e) : d * (a * f - b * e) = 0 := by
  sorry
example {u v : ℝ} (h₁ : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by
  sorry
example {z : ℝ} (h₁ : z ^ 2 + 1 = 0) : z ^ 4 + z ^ 3 + 2 * z ^ 2 + z + 3 = 2 := by
  sorry
example {p q r : ℚ} (h₁ : p + q + r = 0) (h₂ : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 := by
  sorry

example {a b : ℂ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 := by
  polyrith
  polyrith
  polyrith
  polyrith
  polyrith
  polyrith
  polyrith
  polyrith
