import Mathlib.Tactic
import LftCM.C11_Algebraic_Geometry.help

set_option autoImplicit false

/-!
In this exercise sheet, you can use the following commands.

They list (most of) the tactics and lemmas that are used in the solutions.
-/
#help
#tactics
#lemmas

example : True := by
  #help
  #tactics
  #lemmas
  trivial

namespace Day4_AG

section Presentation
/-!
#  Algebraic geometry -- preliminaries

The exercises cover several different notions:
* `RingHom`s `f : R →+* S`;
* `Polynomial` rings  `R[X]`;
* `AddMonoidAlgebra`s `AddMonoidAlgebra A R` (close to the group algebra $R[A]$);
* `natDegree`s of `Polynomial`s.

I will certainly not have time to talk about all of the above, but you are of course more than
welcome to explore on your own and to ask lots of questions!

##  `RingHom`

These "bundled" morphisms should have been covered in a previous tutorial.
I won't say more now, unless there are questions!

##  `AddMonoidAlgebra`

The structure `AddMonoidAlgebra` is `Mathlib`s formalization of the concept of a group ring.
For instance, if `G` is a group and `k` is a field, then `AddMonoidAlgebra k G` is the ring
of formal finite linear combinations of elements of `G` with coefficients in `k`.

The notation `k[G]` is fairly standard in mathematics for this notion.
We introduce it specifically for this exercise sheet:
`Mathlib`s notation is the unabridged `AddMonoidAlgebra k G`.

##  `Polynomial`

The structure `Polynomial` takes a (Semi)`Ring` as input and returns...
the `Mathlib` formalization of polynomials!
-/

section Polynomials

variable {R : Type*} [Semiring R] {r : R}

#check Polynomial R
#guard_msgs(drop error) in
#check R[X]

open Polynomial

#check R[X]
#guard_msgs(drop error) in
#check R[Y]

-- ##  Basic constructors

-- ###  `C` -- the constants
-- the extended name is `Polynomial.C`
#check C r

example {s : R} : C (r * s) = C r * C s := by
  exact?

-- ###  `X` -- the variable
-- the extended name is `Polynomial.X`
#check (X : R[X])
#check X

-- ###  `monomial` -- the... monomials
-- we are not actually going to use them
#check monomial 3 r

example {n : ℕ} : C r * X ^ n = monomial n r := by
  exact?

example : ((X + C 1) ^ 2 : R[X]) = X ^ 2 + 2 * X + 1 := by
  rw [sq, mul_add, add_mul, add_mul, ← sq, add_assoc, add_assoc]
  simp     -- clears the `C`s
  congr 1  -- matches the common parts of the expressions
  rw [← add_assoc, two_mul]

example : ((X + C r) ^ 2 : R[X]) = X ^ 2 + 2 * C r * X + C r ^ 2 := by
  rw [sq, mul_add, add_mul, add_mul, ← sq, add_assoc, add_assoc, X_mul_C]
  congr 1  -- matches the common parts of the expressions
  rw [← add_assoc, two_mul, ← add_mul, sq]

variable {S} [CommSemiring S] in
example : ((X + 1) ^ 2 : S[X]) = X ^ 2 + 2 * X + 1 := by
  ring

variable {S} [CommSemiring S] in
example : ((X + C 1) ^ 2 : S[X]) = X ^ 2 + C 2 * X + C 1 := by
  simp?
  ring

#check natDegree

--  Lean may not always have enough information to fill in typeclass arguments
#guard_msgs(drop error) in
example : natDegree 1 = 0 := by
  exact?

#guard_msgs(drop error) in
example : natDegree (C r * X + C 1) = 1 := by
  exact?  -- we are missing a hypothesis!

--  prove using `natDegree_add_eq_left_of_natDegree_lt`
example [Nontrivial R] : natDegree (X + C 1) = 1 := by
  rw [natDegree_add_eq_left_of_natDegree_lt]
  exact?
  simp?

--  One thing that could be useful for some of the exercises.
--  The evaluation of polynomials in `R[X]` at a fixed polynomial `p` is a ring homomorphism
--  `R[X] →+* R[X]`.
--  This is called `Polynomial.aeval` in `Mathlib`.

noncomputable
example {R} [CommRing R] (p : R[X]) : R[X] →+* R[X] :=
(aeval p).toRingHom

/-
###  Pitfall: disappearing `C`s

The exact shape of a lemma in `Mathlib` is what makes it applicable or not in any given situation.
On the one hand, not all combinations of lemmas with/without `C` in statements about `Polynomial`s
are available.
On the other hand, `simp` will try to remove `C`s in your expressions, if it can.
This means that `exact?` might have found a lemma *before* applying `simp` and may fail afterwards:
-/
example [Nontrivial R] : natDegree (X + C 1) = 1 := by
  --simp  --uncomment this `simp` and `exact?` fails
  exact?

end Polynomials

section AddMonoidAlgebra
variable {R A} [CommRing R] [AddMonoid A] {r : R} {a : A}

open AddMonoidAlgebra

#guard_msgs(drop error) in
#check R[A]

local notation R "[" A "]" => AddMonoidAlgebra R A
--  With this notation, the following works:
#check R[A]

-- ##  Basic constructors

-- ###  `single` -- a single term
-- fully qualified name: `AddMonoidAlgebra.single`
-- Mathematically, you would probably write this as $r a$ or $r [a]$ if you wanted to
-- maintain the distinction between the element $a ∈ A` and the corresponding $[a] ∈ k[A]$
#check single a r
-- *Warning.*  The `Mathlib` convention of ordering the arguments is backwards with respect to
-- what I would expect!

example : single (0 : A) (0 : R) = 0 := by
  exact?

example : single (0 : A) (1 : R) = 1 := by
  exact?

-- ###  `of` -- the bundled version of `a ↦ single a 1`
-- `AddMonoidAlgebra.of R A` is the homomorphism that embeds `A` into `R[A]`.
-- Since the operations that `of` preserves are addition on `A` and multiplication on `R[A]`,
-- the actual implementation adds an extra layer relabeling `+` on `A` to `*`.
#check of R A

example : single a 1 = of R A a := by
  exact?

example {b : A} {s : R} : single a r * single b s = single (a + b) (r * s)  := by
  exact?

example {b : A} : of R A (a + b) = of R A a * of R A b := by
  apply (map_mul (of R A))
  --apply map_mul -- also works

/-
In this exercise sheet, there are no more uses of `of`.
-/

example : (single (1 : ZMod 2) (1 : R)) ^ 2 = 1 := by
  rw [sq, single_mul_single]
  simp
  rfl

example {n : ℕ} : (single (1 : ZMod n) (1 : R)) ^ n = 1 := by
  rw [single_pow]
  simp
  rfl

/-
###  `AddMonoidAlgebra` and `Polynomial`

Informally, the polynomial ring `R[X]` is the same as the (add) monoid algebra `R[ℕ]`.
Formally, the isomorphism between them is called `Polynomial.toFinsuppIso`
-/
open Polynomial in
example : R[X] ≃+* R[ℕ] := by exact toFinsuppIso R
/-
If you care about these implementation details,
* `AddMonoidAlgebra R A` is just a Type synonym of finitely supported functions `A →₀ R`;
* `Polynomial R` is a `structure` containing a term of an `AddMonoidAlgebra`.
-/
end AddMonoidAlgebra

end Presentation

section Exercises
/-
# Exercises

The exercises introduce an alternative notation for `RingHom`.
The notation is `Spec R (S)`, where `R` and `S` are rings.
The displayed parentheses in the notation are not optional.
The notation is inspired by algebraic geometry, where the `S`-valued points
of `Spec R` are denoted by precisely this notation
and exactly mean "the ring homomorphisms from `R` to `S`".

You will compute `Spec ℤ (R)` for any `R`,
and you will prove that `Spec ℚ[x]/(x^2-1) (ℚ)` has at most two elements.
In the exercises, this last result uses two facts.
First, the isomorphism
`ℚ[x]/(x^2-1) ≃ ℚ [ℤ/2ℤ]`
where the right hand ring is `AddMonoidAlgebra ℚ (ZMod 2)`,
the group algebra on the group with two elements.
Second, the Type `Bool` of `Bool`eans whose only terms are `true` and `false`.
You will prove that `Spec ℚ (AddMonoidAlgebra ℚ (ZMod 2))`
injects into `Bool`.
-/

section RingHoms
/-
##  Part 1 -- `RingHom` and points

The tactics/commands `#help, #tactics, #lemmas` list tactics and lemmas that are probably
sufficient to solve all the exercises.

We begin with some examples to get familiar with `RingHom`, but thinking them as
morphisms of `Scheme`s.
As you can see, this is just notation, but it might guide your intuition.
Thus, you should be able to treat `Spec` in exactly the same way as you treat `RingHom`s.
-/

variable (R S : Type*) [CommRing R] [CommRing S] in
/-- `Spec R (S)` is the Type of all `S`-valued points of `Spec R`.

Implementation detail: this is just a synonym for `R →+* S`, the type of
ring homomorphisms from `R` to `S`. -/
notation "Spec " R :max " (" S ") " => R →+* S

variable {R : Type*} [CommRing R]

/- `Spec ℤ` has a unique `R`-valued point for every (commutative unital) ring `R`.
The standard name for this "point" is `Int.castRingHom R`. -/
lemma Spec_Int_eq (f : Spec ℤ (R)) : f = Int.castRingHom R := by
  sorry

/-  Now with `ℚ`: `Spec ℚ` has a unique `R`-valued point for every `ℚ`-algebra `R`.
The standard name for this "point" is `Algebra.toRingHom`. -/
example [Algebra ℚ R] (f : Spec ℚ (R)) : f = Algebra.toRingHom := by
  sorry

/-  the definition of `ZMod n` is "by cases": when `n = 0`, `ZMod n = ℤ`,
otherwise, `ZMod n` is represented by the natural numbers in `{0,...,n-1}`. -/
example {n : ℕ} {a : ZMod n} : ∃ m : ℤ, m = a := by
  sorry

/-  `Mathlib` already contains this lemma, unsurprisingly! -/
example {n : ℕ} [NeZero n] : Function.Surjective (Nat.cast (R := ZMod n)) := by
  sorry

example {n : ℕ} (f : Spec (ZMod n) (ZMod n)) : f = RingHom.id (ZMod n) := by
  sorry

end RingHoms

section AddMonoidAlgebra
/-
##  Part 2 -- `AddMonoidAlgebra`
-/

open AddMonoidAlgebra

variable {R A} [CommRing R] [AddMonoid A]

local notation R "[" A "]" => AddMonoidAlgebra R A

/-- Given an `R`-valued point `f` of `Spec (R[ZMod 2])` (i.e. a ring homomorphism
`f : R[ZMod 2] →+* R`), `eq_one? f` is the statement that the value of `f` at
`[1 mod 2]` equals `1`.
-/
def eq_one? (R) [CommRing R] (f : Spec (R[ZMod 2]) (R)) : Prop :=
f (single 1 1) = 1

lemma single_one_one_pow_two (f : Spec (R[ZMod 2]) (R)) :
    (f (single 1 1)) ^ 2 = 1 := by
  sorry

lemma single_one_one_eq [NoZeroDivisors R] (f : Spec (R[ZMod 2]) (R)) :
    (f (single 1 1)) = 1  ∨  (f (single 1 1)) = - 1 := by
  sorry

example : Function.Injective (eq_one? ℚ):= by
  sorry

--  What would you need to change if you wanted to replace `ℚ` by a general `CommRing R`?

--  Proving that `eq_one?` is also surjective would require a bit more work!
--  Feel free to try it!  It might be useful to define the two homomorphisms explicitly beforehand.

end AddMonoidAlgebra

section Polynomials
/-!
##  Part 3 -- `Polynomial`s
-/

open Polynomial

variable {R : Type*} [CommRing R]
/-!
Polynomials in Mathlib are denoted by the familiar notation `R[X]`.
This notation is available because of the line `open Polynomial` just inside this section.
Without `open Polynomial`, the notation is `Polynomial R`.

Note that the `R` in `R[X]` is a `CommRing` and you can replace it by whatever (Semi)ring you want.
The `[X]` part is hard-coded: it instructs Lean to consider polynomials in one variable over `R`.
For instance, `#check R[Y]` yields an `unknown identifier 'Y'` error.

Of course, the name of the variable in `R[X]` is `X`, so the notation is internally consistent,
but you do not get the option of changing it, at least not easily!

Also, the "obvious" inclusion `R ↪ R[X]` is denoted by `C` (for `C`onstants).
The full name is `Polynomial.C`, but we are inside `open Polynomial`, so `C` suffices.

Thus, `X ^ 3 + C 3 * X - C 2` represents the polynomial that you might write in TeX as
$x ^ 3 + 3 x - 2$.
-/

--  Hint: `aeval` could be useful here!
example : ∃ f : Spec ℤ[X] (ℤ[X]), f ≠ RingHom.id ℤ[X] := by
  sorry

variable (R) in
/- The evaluation at a fixed element of `R` is a ring homomorphism `ℤ[X] →+* R`. -/
def eval_at (r : R) : Spec ℤ[X] (R) := (aeval r).toRingHom

lemma eval_at_injective : Function.Injective (eval_at R) := by
  sorry

lemma eval_at_surjective : Function.Surjective (eval_at R) := by
  sorry

/-- The `R`-valued points of `𝔸 ^ 1` are in bijection with `R`. -/
lemma eval_at_equiv : R ≃ Spec ℤ[X] (R) := by
  sorry

--  The following exercises get you familiar with `natDegree`s of polynomials.
section natDegree

example : natDegree (X + 1 : ℤ[X]) = 1 := by
  sorry

example : natDegree (C 0 * X ^ 2 + C 3 * X : ℤ[X]) = 1 := by
  sorry

example (h2 : (2 : R) = 0) (h3 : (3 : R) = 0) : (0 : R) = 1 := by
  sorry

lemma aux [Nontrivial R] (h2 : (2 : R) ≠ 0) :
    natDegree (C 4 * X ^ 2 : R[X]) < natDegree (C 2 * X ^ 3 : R[X]) := by
  sorry

/-- Proof without automation -- I had prepared this before tactic `compute_degree` was merged. -/
example : natDegree (C 2 * X ^ 3 + C 4 * X ^ 2 + 1 : R[X]) ∈ ({0, 3} : Set ℕ) := by
  sorry

/-- Proof with more automation -- works now that `compute_degree` is merged. -/
example : natDegree (C 2 * X ^ 3 + C 4 * X ^ 2 + 1 : R[X]) ∈ ({0, 3} : Set ℕ) := by
  sorry

end natDegree

end Polynomials

end Exercises

end Day4_AG
