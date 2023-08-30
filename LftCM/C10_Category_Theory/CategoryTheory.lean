import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Algebra.Category.GroupCat.Basic

open CategoryTheory

/-!
# Category Theory

* Acknowledgements: I only contributed miniscule amounts to the category theory library. It's
maintained by Reid Barton, Riccardo Brasca, Johan Commelin, Markus Himmel, Bhavik Mheta, Scott Morrison,
Joël Riou, and Adam Topaz.

## Challenges

Category is generally regarded a *challenging field* to formalise for several reasons:
* We need dependent types because we don't want a plain type of morphisms: -/
  structure FlatCat  where
    Obj : Type u
    Mor : Type v
    dom : Mor → Obj
    cod : Mor → Obj
    id : Obj → Mor
    id_dom : dom (id X) = X
    id_cod : cod (id X) = X
    -- ...
  /-! but instead -/
  structure NonFlatCat where
    Obj : Type u
    Mor : Obj → Obj → Type v
    id : (X : Obj) → Mor X X
    -- ...
/-!
* Need categories to be doubly universe polymorphic!
* "Silent" reassociation and application of unit laws in proofs.
* Frequent usage of "canonical this and that" -- being *a limit* vs. being *the limit*.
* Use of dependent types means that we have to be very hygienic about not using equalities between
  objects.
* That's not even starting to touch the pain of formalising *higher* category theory.

## Overview of the Basic Notions

### Categories, Functors
-/

open Category CategoryTheory Limits

section

variable {C : Type} [Category C] {W X Y Z : C}

#check @Category
#check CategoryTheory.Functor
#check _ ⟶ _  -- Type morphisms using \hom
#check _ ≫ _  -- Type composition using \gg

/-
### Limits

Now we need concrete universes. Always list morphism universes *first*
-/
universe v v' u u'

#check IsLimit  -- Note that this is not a proposition!!
#check HasLimit
#check HasLimitsOfShape
#check HasLimitsOfSize.{v', u'}
#check HasLimits

/-
Let's look at binary products as an example.
-/
#check HasBinaryProduct X Y
#check HasBinaryProducts


/-
## Useful Tactics and Macros

The slice tactic can be used to
-/

example (l : Z ⟶ W)
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (g' : W ⟶ Y) (e : f ≫ g = g') :
    l ≫ (f ≫ (g ≫ h)) = (l ≫ g') ≫ h := by
  slice_lhs 2 3 =>
    rw [e]
  rw [assoc]

-- TODO `aesop_cat`

/-
Another tool for handling associativity is the macro `reassoc_of%` which creates a reassociated
version of a given equality:
-/
theorem reassoc_of_example {f g : X ⟶ Y} (e : f = g) (h : Y ⟶ Z) :
    f ≫ h = g ≫ h :=
  (reassoc_of% e) h
/- The same can be achieved adding `@[reassoc]` in front of a theorem.

A similiar attribtue is `@[elementwise]` which, for a theorem `foo` which is an equality between
morphisms, adds a theorem `foo_apply` stating the elementwise equality instead.
-/

end

/-
## The Current State of Formalization
-/
#check yoneda
#check Yoneda.yonedaFull
#check Yoneda.yoneda_faithful
-- TODO add overview on what's already formalized

/- Category instantiations can be found in other folders, e.g. `Algebra.Category`  -/
#check GroupCat  -- The category of groups
