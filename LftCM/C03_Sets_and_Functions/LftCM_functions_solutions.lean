/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import Mathlib.Tactic

/-!

# Functions in Lean.

Notation for functions is the usual in mathematics: given two types `X` and `Y`, `f : X → Y`
denotes a function from `X` to `Y`.

Internally, `X → Y` denotes the type of functions from `X` to `Y`, and `f : X → Y` means that  `f`
is a term of type `X → Y`, that is, a function from `X` to `Y`.

NOTATION: given `x : X` and `f : X → Y`, to denote the evaluation `f(x)` we can (and usually do)
omit the parenthesis, and write `f x`. However, the parenthesis are needed for more complicated
expressions. For instance, given `x : X`, `f : X → Y` and `g : Y → Z`, to evaluate the
composition `g(f(x))` we need at least the exterior parentheses: `g(f x)`.

WARNING: Given `a b : X` and `f : X → Y`, if we write `f a + b`, Lean will interpret this as
`f(a) + b` (which in general will cause a type error). If we mean `f(a + b)`, we need to
write the parentheses.
-/

section

variable (X Y Z : Type) [AddMonoid X] (a b : X) (f : X → Y) (g : Y → Z)
#check f a
--#check g f a
#check g (f a)
--#check f a + b
#check f (a + b)

end


/-!
## Injectivity and Surjectivity

Lean knows the definition of injective function (`Function.Injective`) and surjective function
(`Function.Surjective`). Given any function `f : X → Y`, `Function.Injective f`
and `Function.Surjective f` are propositions (whose truth value depends on `f`).

-/

/- If we open the "Function" `namespace`, we can omit `Function.` and simply write
`Injective f` and `Surjective f`. -/

open Function


/- We fix three types `X`, `Y`, `Z` (we can think of them as sets) and two functions
`f : X → Y`, `g : Y → Z`. -/
variable {X Y Z : Type} {f : X → Y} {g : Y → Z}

/- Let `a,b,x` be elements of `X`, `y ∈ Y`, `z ∈ Z`. -/
variable (a b x : X) (y : Y) (z : Z)

-- We open a `namespace` to avoid name clashes with existing Mathlib lemmas.
namespace functions

/-!
# Injective functions
-/

/- We check Lean's definition of injective function. -/
lemma injective_def : Injective f ↔ ∀ a b : X, f a = f b → a = b := by
  rfl -- true by definition

-- The instruction `rw [injective_def]` replaces `Injective f` by its definition

/- We check that the identity function ` id : X → X` is given by `id(x) = x`. -/
lemma id_eval : id x = x := by
  rfl -- true by definition

-- Function composition is denoted by `∘`. By definition, `(g ∘ f) (x) = g(f(x))`.
lemma comp_eval : (g ∘ f) x = g (f x) := by
  rfl

/- We are proving these lemmas that are true "by definition" (`rfl`) so that we can use the `rw`
tactic to replace these terms by their definition.-/

/- For example, we can start this proof with `rw [injective_def]`, and later use `rw [id_eval]`. -/
lemma injective_id : Injective (id : X → X) := by
  rw [injective_def]
  intro x y hxy
  rw [id_eval x] at hxy
  rw [id_eval y] at hxy
  exact hxy

/-- A composition of injective functions is injective. -/
lemma injective_comp (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  rw [injective_def] at *
  intros x y hxy
  apply hf
  apply hg
  exact hxy

/- Exercise-/
example (f : X → Y) (g : Y → Z) :
  Injective (g ∘ f) → Injective f := by
  intro h x y hxy
  apply h
  rw [comp_eval]
  rw [hxy]
  rfl


/-!

### Surjective functions

-/

/- We check Lean's definition of surjective function. -/
lemma surjective_def : Surjective f ↔ ∀ y : Y, ∃ x : X, f x = y := by
  rfl

/-- The identity function is surjective. -/
lemma surjective_id : Surjective (id : X → X) := by
  intros x
  use x
  rw [id_eval] -- or `rfl`


/-- A composition of surjective functions is surjective. -/
lemma surjective_comp (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  intro z
  cases' hg z with y hy
  cases' hf y with x hx
  use x
  rw [comp_eval]
  rw [hx]
  rw [hy]

/- Example -/
example (f : X → Y) (g : Y → Z) :
  Surjective (g ∘ f) → Surjective g := by
  intros h z
  cases' (h z) with x hx
  use (f x)
  exact hx

/-!
### Bijective functions
-/

/- A bijective function is, by definition, a function that is both injective and surjective. -/
lemma bijective_def : Bijective f ↔ Injective f ∧ Surjective f := by
  rfl

/-- the identity function is bijective -/
lemma bijective_id : Bijective (id : X → X) := by
  rw [bijective_def]
  constructor
  . exact injective_id
  . exact surjective_id

/-- A composition of bijective functions is bijective. -/
lemma bijective_comp (hf : Bijective f) (hg : Bijective g) : Bijective (g ∘ f) := by
  cases' hf with hf_inj hf_surj
  cases' hg with hg_inj hg_surj
  exact ⟨injective_comp hf_inj hg_inj, surjective_comp hf_surj hg_surj⟩


/- ###  λ notation:
In Lean, functions are defined using `λ` expressions:
`λ x ↦ f x` is a function that maps `x` to `f (x)`
-/

def α : ℕ → ℕ := λ n ↦ n^2 + 3 -- `f(n) = n^2 + 3`

-- We can also use the keyword `fun` instead of `λ`

def α' : ℕ → ℕ := fun n ↦ n^2 + 3

example : α 3 = 12 := by
  rw [α]
  rfl

/-!
### Working with a concrete example

Some useful lemmas to complete the following examples are:
* **not_forall** : `(¬∀ x, p x) ↔ ∃ x, ¬p x`
* **add_left_inj** : `∀ x y z, x + z = y + z ↔ x = y`
* **Nat.succ_ne_zero** : `∀ (n : ℕ), n.succ ≠ 0`: here it is crucial to understand that `x ≠ y`
is *defined* as the implication ` (x = y) → false`, `n.succ = n + 1` *by definition*
(whereas `1 + n = n.succ` is a *theorem*).
-/

def s : ℕ → ℕ := fun n ↦ n + 1

example : Injective s := by
  rw [injective_def]
  intro n m h
  rw [s, s, add_left_inj] at h
  exact h

example : ¬ Surjective s := by
  rw [surjective_def, not_forall]
  use 0
  rw [not_exists]
  intro n
  rw [s]
  exact Nat.succ_ne_zero n

end functions
