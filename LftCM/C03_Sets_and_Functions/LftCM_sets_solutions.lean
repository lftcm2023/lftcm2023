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
  rfl

/- In this lemma, after writing `rw [subset_def] at *`, the hypothesis `hYZ` becomes
`hYZ : ∀ (a : Ω), a ∈ Y → a ∈ Z` (and similarly for `hXY`).
Since `hYZ` is an implication, once we reduce the goal to `a ∈ Z`, we can make progress by using
`apply hYZ`.
Frequently, it is useful to think of `hYZ` as a function which, given a term `a` of type `Ω`
and a proof `haY` that `a ∈ Y`, returns a proof `haZ` of `a ∈ Z`.
-/
lemma subset_trans (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z := by
  rw [subset_def] at *
  intro a ha
  apply hYZ
  exact hXY a ha

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
  ext a
  constructor
  . apply hXY
  . apply hYX

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
  intro x hx
  rw [union_def]
  left
  exact hx

lemma subset_union_right : Y ⊆ X ∪ Y := by
  intro y hy
  right
  assumption

lemma union_self : X ∪ X = X := by
  ext x
  rw [union_def]
  /- We could finish with `rw or_self`, but for practice, let's do: -/
  constructor <;> -- `<;>` means that the next tactic will be applied to all the open goals.
  intro hX
  . cases' hX with hX hX <;>
    exact hX
  . left
    exact hX

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z := by
  constructor
  . intro h
    constructor
    . intro x hx
      apply h
      exact subset_union_left Ω X Y hx
    . intro y hy
      apply h
      right
      assumption
  . rintro ⟨hXZ, hYZ⟩ a (haX | haY)
    . exact hXZ haX
    . exact hYZ haY

variable (W : Set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z := by
  rintro a (haW | haY)
  . left
    exact hWX haW
  . right
    exact hYZ haY

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z := by
  apply union_subset_union
  . exact hXY
  . exact subset_refl Ω Z

/- Intersections -/

lemma inter_subset_left : X ∩ Y ⊆ X := by
  rintro x ⟨hxX, _hxY⟩
  exact hxX

lemma inter_self : X ∩ X = X := by
  ext x
  constructor
  . rintro ⟨hx, -⟩
    exact hx
  . intro hx
    exact ⟨hx, hx⟩

lemma inter_comm : X ∩ Y = Y ∩ X := by
  ext
  constructor
  . rintro ⟨hX, hY⟩
    exact ⟨hY, hX⟩
  . rintro ⟨hY, hX⟩
    exact ⟨hX, hY⟩

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z := by
  ext
  constructor
  . rintro ⟨hX, ⟨hY, hZ⟩⟩
    exact ⟨⟨hX, hY⟩, hZ⟩
  . rintro ⟨⟨hX, hY⟩, hZ⟩
    exact ⟨hX, ⟨hY, hZ⟩⟩

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
  rw [mem_def]
  exact Nat.prime_three


def is_even (n : ℕ) : Prop := ∃ t, n = 2 * t

example : 42 ∈ {n : ℕ | is_even n} := by
  rw [mem_def]
  use 21

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
  intro a ha
  rw [Set.mem_preimage]
  use a

example : f '' (f ⁻¹' T) ⊆ T := by
  intro b hb
  rw [Set.mem_image] at hb
  obtain ⟨a, ha, hab⟩ := hb
  rw [Set.mem_preimage] at ha
  rwa [← hab]

example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  . intro h s hs
    rw [Set.mem_preimage]
    apply h
    use s
  . rintro h t ⟨s, hs, rfl⟩
    exact h hs

/-!
### Universal and existencial quantifiers
-/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) := by
  constructor
  . intro hX b hb
    apply hX
    use b
  . intro h1 h2
    cases' h2 with b hb
    exact h1 b hb

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) := by
  constructor
  . intro hX
    by_contra hnX
    apply hX
    intro a
    by_contra ha
    apply hnX
    use a
  . rintro ⟨b, hb⟩ hX
    exact hb (hX b)

end sets
