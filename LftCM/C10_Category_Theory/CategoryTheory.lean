import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Algebra.Category.Ring.Basic

set_option autoImplicit true

open CategoryTheory

/-!
# Category Theory

* Acknowledgements: I only contributed miniscule amounts to the category theory library. It's
maintained by Reid Barton, Riccardo Brasca, Johan Commelin, Markus Himmel, Bhavik Mheta, Scott Morrison,
Joël Riou, and Adam Topaz.

## Challenges

Category is generally regarded a *challenging field* to formalise for several reasons:
* We need dependent types because we don't want a plain type of morphisms:
-/
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
* UMPs are actually a whole collection of statements:
  Existence of an object, of morphisms, and uniqueness in form of a (unique) isomorphism

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

example (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ 𝟙 Y ≫ g = f ≫ g := by simp

example {X : C} : C ⥤ Type where
  obj := fun Y => X ⟶ Y
  map := fun f g => g ≫ f  -- The remaining fields are solved automatically!

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

-- TODO examples for `aesop_cat`

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
## The Current Extent of Formalization
-/
#check yoneda
#check Yoneda.yonedaFull
#check Yoneda.yoneda_faithful
-- TODO add overview on what's already formalized

/- Category instantiations can be found in other folders, e.g. `Algebra.Category`  -/
#check GroupCat  -- The category of groups
/-
* (Co)homology of chain complexes in `Algebra.Homology.Homology`
* Abelian categories

## Exercises

### Exercise 1: On the Yoneda embedding
-/

section

open Opposite

variable (C : Type u) [Category.{v} C]

def isoOfHomIso {X Y : C} (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y where
  hom := (h.app (op X)).hom (𝟙 X)
  inv := (h.app (op Y)).inv (𝟙 Y)

end

/-
### Exercise 2: Polynomials on Rings are a Functor
-/
section

noncomputable def RingCat.Polynomial : RingCat ⥤ RingCat where
  obj R := .of (_root_.Polynomial R)
  map f := Polynomial.mapRingHom f
  map_id R := by
    ext
    have : (𝟙 R) = RingHom.id R := rfl  -- TODO this wasn't necessary in Lean 3
    aesop_cat
  map_comp f g:= by
    ext r
    have : f ≫ g = g.comp f := rfl
    simp only [comp_apply]
    rw [this, Polynomial.coe_mapRingHom, Polynomial.coe_mapRingHom, Polynomial.coe_mapRingHom]
    simp [Polynomial.map_map]

end

/-
### Exercise 3: Equivalences and Monos
-/
section

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

theorem equiv_reflects_monos {X Y : C} (f : X ⟶ Y) (e : C ≌ D) (hef : Mono (e.functor.map f)) :
    Mono f := by
  aesop_cat

end

/-
### Exercise 4: Representables
-/
section

open Polynomial

#check Polynomial.eval₂
#check Polynomial.eval₂RingHom
#check NatTrans

theorem CommRing.forget_representable : Functor.Corepresentable (forget CommRingCat.{0}) where
  has_corepresentation := ⟨.op (.of (Polynomial ℤ)),
    { app := fun R f => by { unfold coyoneda at f; dsimp at f; exact f X } },
    ⟨{ app := fun R r => Polynomial.eval₂RingHom (algebraMap ℤ R) r
       naturality := by
        simp only [coyoneda_obj_obj, Opposite.unop_op, CommRingCat.forget_map, algebraMap_int_eq]
        intro X Y f
        ext
        simp only [types_comp_apply, coyoneda_obj_map, Opposite.unop_op, comp_apply]
        rw [coe_eval₂RingHom, coe_eval₂RingHom, eval₂_eq_sum, eval₂_eq_sum]
        simp [sum, map_sum] },
      by  ext R a
          change @Eq (_ →+* _) _ _
          aesop_cat,
      by  ext R a
          change @Eq R _ _
          simp
          rw [coe_eval₂RingHom]
          aesop_cat ⟩⟩

end

#check RingHom.map_sum

#check Functor.Corepresentable

/-
### Exercise 6: Pushouts and Epis

Let C be a category, X and Y be objects and f : X ⟶ Y be a morphism. Show that f is an epimorphism
if and only if the diagram

X --f--→ Y
|        |
f        𝟙
|        |
↓        ↓
Y --𝟙--→ Y

is a pushout.
-/
section

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C]

def pushoutOfEpi {X Y : C} (f : X ⟶ Y) [Epi f] :
    IsColimit (PushoutCocone.mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f) := by
  fapply PushoutCocone.IsColimit.mk
  · intro s; exact s.ι.app WalkingSpan.left
  · intro s
    aesop_cat
  · intro s
    have snd := s.ι.naturality WalkingSpan.Hom.snd
    simp only [span_zero, Functor.const_obj_obj, span_right, span_map_snd, PushoutCocone.ι_app_right,
      PushoutCocone.condition_zero, Functor.const_obj_map, comp_id] at snd
    rw [cancel_epi] at snd
    aesop_cat
  · intro s
    aesop_cat

end
