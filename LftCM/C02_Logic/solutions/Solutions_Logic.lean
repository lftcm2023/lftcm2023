import Mathlib.Data.Real.Basic

set_option autoImplicit true

/-
# Logics

* Get used to be precise about logical connective, phrases like "to prove
  `A ∧ B` we have to prove `A` and `B`." are awkward but necessary.

Overview of the most important connectives:

→   \to     if ... then ...           implication
∀   \all    for all                   universal quantification
∃   \ex     there exists              existential quantification
¬   \not    not                       negation
∧   \and    and                       conjunction
∨   \or     or                        disjunction
↔   \iff    ... if and only iff ...   biimplication
False       contradiction!            falsity
True        this is trivial           truth

... and how to use them:

                appearing as hypothesis `h`                   appearing as goal
`A → B`         `have h' := h ha`, `apply h`                  `intro ha`
`∀ x, P x`      `have h' := h x`, `apply h`, `specialize`     `intro x`

`A ∧ B`         `rcases h with ⟨ha, hb⟩`, `h.1`, `h.2`        `constructor`
`A ∨ B`         `rcases h with (ha | hb)`                     `left` or `right`
`∃ x. P x`      `rcases h with ⟨x, hx⟩`                       `constructor` or `use x`

`False`         `contradiction`                               --
`True`          --                                            `trivial`

`¬ A`           `contradiction`                               `intro ha`
`A ↔ B`         `rcases h with ⟨h₁, h₂⟩`                      `constructor`

* `by_contra` for proofs by contradiction
* Note that logical connectives can be hidden under other definitions:
  `a ∣ b` is existential, `s ⊆ t` is universal.
-/

/-!
## Implication and universal quantifiers
-/

theorem my_add_le_add (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) :
    x + z ≤ y + w :=
  add_le_add h₁ h₂

section

variable (a b c d : ℝ)
variable (h₁ : a ≤ b) (h₂ : c ≤ d)

#check my_add_le_add
#check my_add_le_add a b
#check my_add_le_add a b c d h₁
#check my_add_le_add _ _ _ _ h₁
#check my_add_le_add _ _ _ _ h₁ h₂

theorem my_add_le_add' {x y z w : ℝ} (h₁ : x ≤ y) (h₂ : z ≤ w) :
    x + z ≤ y + w :=
  add_le_add h₁ h₂

#check my_add_le_add' h₁
#check my_add_le_add' h₁ h₂

end

def fnUB (f : ℝ → ℝ) (a : ℝ) := ∀ x, f x ≤ a

section

-- Demonstrate use of `apply`, `have`, `specialize`, `dsimp`, proof structuring
-- Also show `have`,

theorem fnUB_add (hfa : fnUB f a) (hgb : fnUB g b) :
    fnUB (f + g) (a + b) := by
  sorry

end

/-!
## The existential quantifier
-/

-- Demonstrate `use`, `refine` and `norm_num`, explain how to know that it is existential

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  sorry

example : 5 ∣ 20 := by
  sorry  -- Automatically closes trivial goals!

-- Demonstrate `rcases` and `obtain` on existential quantifiers

section

def fnHasUB (f : ℝ → ℝ) := ∃ a, fnUB f a

example (ubf : fnHasUB f) (ubg : fnHasUB g) : fnHasUB (f + g) := by
  sorry

end

/-
The existential quantifier in Lena comes with an axiom called *global choice*.
It provides a witness for all proofs of existentially quantified statements and
guarantees that the witness is the same if we deconstruct the same statement twice.
-/
#check Exists.choose
#check Exists.choose_spec

noncomputable def chooseNat (h : ∃ (x : ℕ), x > 4) : ℕ := sorry

/-!
## Negation

`¬ A` is an abbreviation for `A → False`.
-/

section

variable {f : ℝ → ℝ}

-- Demonstrate `rintro`

example (h : ∀ a, ∃ x, f x > a) : ¬ fnHasUB f := by
  sorry

-- Repeat with demonstration of `simp`, `simp only`, `push_neg`

example (h : ∀ a, ∃ x, a < f x) : ¬ fnHasUB f := by
  sorry

end

/-!
## Conjuction
-/

section

variable {x y : ℝ}

-- Demonstrate `constructor`, `linarith`, `subst`, `contradiction`

example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y := by
  sorry

-- Demonstrate `rcases`, `.1`,

example (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  sorry

end

/-!
## Disjunction
-/

section

variable (x y z : ℝ)

-- Demonstrate `library_search`, `rcases`, `left`, `right`, `rwa`

#check abs_of_nonneg
#check abs_of_neg

example : x < |y| → x < y ∨ x < -y := by
  sorry

-- Demonstrate nested `rcases`

example (h : (x < y ∧ y < z) ∨ x < z) : x < z := by
  sorry

end




















/-!
## More exercises
-/

section

variable (p q : Prop) -- Propositions
variable (r s : ℕ → Prop)  -- Predicates over the natural numbers

example : p ∧ q → q ∧ p := by
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  exact ⟨hq, hp⟩

example : p ∨ q → q ∨ p := by
  intro hpq
  rcases hpq with (hp|hq)
  · right
    assumption
  · left
    assumption

example : (∃ x, r x ∧ s x) → (∃ x, r x) ∧ (∃ x, s x) := by
  intro h
  rcases h with ⟨x, hrx, hsx⟩
  constructor
  · use x
  · use x

example : ∀ z, (∃ x y, r x ∧ s y ∧ y = z) → ∃ x, r x ∧ s z := by
  intro z h
  rcases h with ⟨x, y, hr, hx, rfl⟩
  use x

example : ¬¬(¬¬p → p) := by
  intro h
  apply h
  intro hnnp
  exfalso
  apply hnnp
  intro hp
  apply h
  intro
  assumption

example : ∃ x, r x → ∀ y, r y := by
  by_cases h : ∀ y, r y
  · use 0
    intro _
    assumption
  · push_neg at h
    rcases h with ⟨w, hw⟩
    use w
    intro hw'
    contradiction

end
