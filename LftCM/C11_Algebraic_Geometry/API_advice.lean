import Mathlib.Tactic
import LftCM.C11_Algebraic_Geometry.help

set_option autoImplicit false

/-!  In this exercise sheet, you can use the following commands.

They list (most of) the tactics and lemmas that are used in the solutions. -/
#help
#tactics
#lemmas

example : True := by
  #help
  #tactics
  #lemmas
  trivial

section Do_not_try_this_at_home

variable (R S : Type*) [CommRing R] [CommRing S]

/-!
# Generic API building advice

##  Float as close as possible to the surface!
-/

namespace Not_a_good_idea
/--
#  Not a good idea!

Our custom version of ring homomorphisms
Note that the order of `R` and `S` is reversed: we input `why R S` and we get out `S →+* R`! -/
def why : Type _ := S →+* R

@[inherit_doc]
local notation "Spec " R :max " (" S ") " => why S R

variable {R S}

/- Let us brute-force our way through this proof! -/
example (f : Spec ℤ (R)) : f = Int.castRingHom (α := R) := by
  unfold why at f  -- unneeded, but you can check that `why` really is `ℤ →+* ℤ` in this case
  rcases f with ⟨f, (h0 : f 0 = 0), (hadd : ∀ x y, f (x + y) = f x + f y)⟩
  -- the previous command breaks up `Spec` (or really `ℤ →+* R`) into
  -- * a multiplicative homomorphism `f : ℤ →* R`
  -- * a proof `h0` that `f` maps `0` to `0`
  -- * a proof `hadd` that `f` is additive
  -- note that `rcases f with ⟨f, h0, hadd⟩` works as well
  -- it just displays `h0, hadd` differently
  -- `rcases f with ⟨⟨f, hmul⟩, h0, hadd⟩`
  -- would have broken `f` further into
  -- * a map `f : OneHom ℤ R` preserving `1` and
  -- * a proof `hmul` of multiplicativity
  -- `rcases f with ⟨⟨⟨f, h1⟩, hmul⟩, h0, hadd⟩`
  -- would have destructured "all the way":
  -- * `f` is a function `ℤ → R`
  -- * `f` is additive `hadd`
  -- * `f` is multiplicative `hmul`
  -- * `f` preserves `0` (`h0`)
  -- * `f` preserves `1` (`h1`)
  congr
  ext n <;> dsimp
  · have : f (-1) + f 1 = f (-1 + 1) := (hadd (-1) 1).symm
    --  replace `simp [h0] at this` by the output of `simp? at this`
    simp only [map_one, add_left_neg, h0] at this
    --  replace `simp` by the output of `simp?`
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_neg, Int.cast_one]
    exact add_eq_zero_iff_eq_neg.mp this

  · simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe,
      Function.comp_apply, eq_natCast, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_ofNat]
    induction n with
      | zero => simpa using h0
      | succ n hn =>
        simp only [Nat.cast_succ]
        dsimp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe] at hadd
        rw [hadd ↑n 1, hn, map_one]

end Not_a_good_idea

/-- `Spec R (S)` is the Type of all `S`-valued points of `Spec R`.

Implementation detail: this is just a synonym for `R →+* S`, the type of
ring homomorphisms from `R` to `S`. -/
notation "Spec " R :max " (" S ") " => R →+* S

--  a much smoother experience!
example (f : Spec ℤ (R)) : f = Int.castRingHom (α := R) := by
  simp

/-!

## Conclusion

Try as much as possible to recycle already existing definitions!
The closer you stay to what is already available, the easier it is to progress.
-/

end Do_not_try_this_at_home
