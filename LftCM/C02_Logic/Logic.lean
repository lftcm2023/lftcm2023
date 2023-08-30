import Mathlib.Data.Nat.Prime
import Mathlib.Data.Real.Basic

/-
# Logics

* Get used to be precise about logical connective, phrases like "to prove `A ∧ B` we have to prove
  `A` and `B`." are awkward but necessary.

Overview of the most important connectives:

→   \to     if ... then ...         implication
∀   \all    for all                 universal quantification
∃   \ex     there exists            existential quantification
¬   \not    not                     negation
∧   \and    and                     conjunction
∨   \or     or                      disjunction
False       contradiction!          falsity
True        this is trivial         truth

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
* Note that logical connectives can be hidden under other definitions: `a ∣ b` is existential,
  `s ⊆ t` is universal.
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
  intro x
  dsimp
  have hfa' : f x ≤ a
  · apply hfa
  specialize hgb x
  apply add_le_add hfa' hgb
  
end

/-!
## The existential quantifier
-/

-- Demonstrate `use`, `refine` and `norm_num`, explain how to know that it is existential

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 2.5
  norm_num 

example : 5 ∣ 20 := by
  use 4  -- Automatically closes trivial goals!

-- Demonstrate `rcases` and `obtain` on existential quantifiers

section

def fnHasUB (f : ℝ → ℝ) := ∃ a, fnUB f a

example (ubf : fnHasUB f) (ubg : fnHasUB g) : fnHasUB (f + g) := by
  rcases ubf with ⟨a, ha⟩
  --rcases ubg with ⟨b, hb⟩
  obtain ⟨b, hb⟩ := ubg
  use a + b
  exact fnUB_add ha hb

end

/-!
## Negation

`¬ A` is an abbreviation for `A → False`.

-/

section

variable {f : ℝ → ℝ}

-- Demonstrate `rintro`?

example (h : ∀ a, ∃ x, f x > a) : ¬ fnHasUB f := by
  intro h₁
  obtain ⟨b, hb⟩ := h₁
  specialize h b
  unfold fnUB at *
  obtain ⟨x, hx⟩ := h
  specialize hb x
  linarith

-- Repeat with demonstration of `simp`, `simp only`, `push_neg`

example (h : ∀ a, ∃ x, f x > a) : ¬ fnHasUB f := by
  dsimp only [fnHasUB, fnUB]
  push_neg
  assumption

end

/-!
## Conjuction
-/

section

variable {x y : ℝ}

-- Demonstrate `constructor`, `linarith`, `subst`, `contradiction`

example (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  · intro he
    subst he
    contradiction

-- Demonstrate `rcases`, `.1`, 

example (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x := by
  rcases h with ⟨h₁, h₂⟩
  contrapose! h₂
  apply le_antisymm h₁ h₂

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
  intro h
  have h₁ : 0 ≤ y ∨ y < 0
  · exact le_or_gt 0 y   
  rcases h₁ with (h₁|h₁)
  · left
    rwa [abs_of_nonneg h₁] at h
  · right
    rwa [abs_of_neg h₁] at h

-- Demonstrate nested `rcases`

example (h : (x < y ∧ y < z) ∨ x < z) : x < z := by
  rcases h with (⟨h₁,h₂⟩|h)
  · apply lt_trans h₁ h₂
  · assumption

end

/-!
## More exercises
-/

section

variable (p q : Prop) -- Propositions
variable (r s : ℕ → Prop)  -- Predicates over the natural numbers

example : p ∧ q → q ∧ p := by
  sorry

example : p ∨ q → q ∨ p := by
  sorry

example : (∃ x, r x ∧ s x) → (∃ x, r x) ∧ (∃ x, s x) := by
  sorry

example : ∀ z, (∃ x y, r x ∧ s y ∧ y = z) → ∃ x, r x ∧ s z := by
  sorry

example : ¬¬(¬¬p → p) := by
  sorry

example : ∃ x, r x → ∀ y, r y := by
  sorry

end
