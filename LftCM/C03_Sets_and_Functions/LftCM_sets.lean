/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import Mathlib.Tactic

/-!
# Sets
-/

/- We define a type `Ω` and three sets `X`, `Y`, `Z` whose elements are of type `Ω`.
  We can think of `X`, `Y`, and `Z` as "subsets" of `Ω`. We also introduce terms
  `a, b, c, x, y, z` of type `Ω`.
 -/
variable (Ω : Type) (X Y Z : Set Ω) (a b c x y z : Ω)

-- We open a `namespace` to avoid conflicts.
namespace sets

/-!

# Subsets

To get the symbol `⊆`, type `\sub` or `\ss`.
-/

-- `X ⊆ Y` means `∀ a, a ∈ X → a ∈ Y`, by definition.

lemma subset_def : X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y := by
  rfl -- by definition

lemma subset_refl : X ⊆ X := by
  sorry

/- In this lemma, after writing `rw [subset_def] at *`, the hypothesis `hYZ` becomes
`hYZ : ∀ (a : Ω), a ∈ Y → a ∈ Z` (and similarly for `hXY`).
Since `hYZ` is an implication, once we reduce the goal to `a ∈ Z`, we can make progress by using
`apply hYZ`.
Frequently, it is useful to think of `hYZ` as a function which, given a term `a` of type `Ω`
and a proof `haY` that `a ∈ Y`, returns a proof `haZ` of `a ∈ Z`.
-/
lemma subset_trans (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z := by
  sorry

/-!
# Set equality
Two sets are equal if and only if they have the same elements.
In Lean, this lemma is called `Set.ext_iff`.
-/

example : X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) := by
  exact Set.ext_iff

/- When we want to reduce the goal `⊢ X = Y` to `a ∈ X ↔ a ∈ Y` for an arbitrary `a : Ω`, we use
  the `ext` tactic. -/

lemma subset.antisymm (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y := by
  sorry

/-!

### Unions and intersections

Notation: type `\cup` or `\un` to obtain `∪`, and `\cap` or `\i` for `∩`

-/

lemma union_def : a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y := by
  rfl

lemma inter_def : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y := by
  rfl

/- Unions. -/

lemma subset_union_left : X ⊆ X ∪ Y := by
  sorry

lemma subset_union_right : Y ⊆ X ∪ Y := by
  sorry -- exercise

lemma union_self : X ∪ X = X := by
  sorry -- exercise

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z := by
  sorry -- exercise

variable (W : Set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z := by
  sorry -- exercise

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z := by
  sorry -- exercise

/- Intersections -/

lemma inter_subset_left : X ∩ Y ⊆ X := by
  sorry

lemma inter_self : X ∩ X = X := by
  sorry -- exercise

lemma inter_comm : X ∩ Y = Y ∩ X := by
  sorry -- exercise

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z := by
  sorry -- exercise

/-!

# Set-builder notation

Given a type `X` and a predicate `P : X → Prop`, the subset of `X` consisting of the terms where
the predicate is true, is `{ x : X | P x }`, and the proof that `a ∈ { x : X | P x } ↔ P a`
is `rfl`.
-/

lemma mem_def (X : Type) (P : X → Prop) (a : X) : a ∈ { x : X | P x } ↔ P a := by
  rfl

/- If you want, you can `rw mem_def` instead. -/

example : 3 ∈ {n : ℕ | Nat.Prime n} := by
  sorry


def is_even (n : ℕ) : Prop := ∃ t, n = 2 * t

example : 42 ∈ {n : ℕ | is_even n} := by
  sorry -- exercise

/-!
### Pushforward and pullback

Let `f : A → B` be a function.

Given a subset `S : set A` of `A`, we can construct the image of `S` under `f`, that is, the subset
`f '' S : set B` of `B` defined as `{b : B | ∃ a : A, a ∈ S ∧ f a = b}`. This is notation for
`Set.image`.

Given a subset `T : Set B` of `B` we can pull it back to make a subset `f ⁻¹' T : Set A` of `A`.
The definition of `f ⁻¹' T` is `{a : A | f a ∈ B}`. This is notation for `Set.preimage`.

-/

variable (A B : Type) (f : A → B) (S : Set A) (T : Set B)

example : S ⊆ f ⁻¹' (f '' S) := by
  sorry

example : f '' (f ⁻¹' T) ⊆ T := by
  sorry -- exercise

example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  sorry -- exercise

/-!
### Universal and existencial quantifiers
-/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) := by
  sorry -- exercise

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) := by
  sorry -- exercises

end sets
