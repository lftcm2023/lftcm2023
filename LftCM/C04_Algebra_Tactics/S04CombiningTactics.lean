/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth, Marc Masdeu
-/
import LftCM.Common
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Subtype
import Mathlib.GroupTheory.GroupAction.Prod
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Polyrith

set_option quotPrecheck false
noncomputable section

/-
Combining Tactics
-------------------

Basics of the field_simp tactic
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


Let us turn to ``field_simp``.  Given a ring expression with division or inversion, this tactic
will clear any denominators for which there is a proof in context that that denominator is nonzero.

Here is an example: we prove that if :math:`a` and :math:`b` are rational numbers, with :math:`a`
nonzero, then :math:`b = a ^ 2 + 3 a` implies :math:`\tfrac{b}{a} - a = 3`.  Check that if you
delete the hypothesis that :math:`a \ne 0` then ``field_simp`` fails to do anything useful.

-/

example (a b : ℚ) (ha : a ≠ 0) (H : b = a ^ 2 + 3 * a) : b / a - a = 3 := by
  field_simp
  linear_combination H

/-
In the following problem we prove that the unit circle admits a rational parametrization:

.. math::

    \left(\frac{m ^ 2 - n ^ 2} {m ^ 2 + n ^ 2}\right) ^ 2
    + \left(\frac{2 m n} {m ^ 2 + n ^ 2}\right) ^ 2 = 1.

Notice
the use of contraposition and of ``(n)linarith`` in proving the nonzeroness hypothesis; these are
both common ingredients. Again, check that if you comment out the justification that
:math:`m ^ 2 + n ^ 2 \ne 0`, then ``field_simp`` fails to trigger.

-/
example (m n : ℝ) (hmn : (m, n) ≠ 0) :
    ((m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2)) ^ 2 + (2 * m * n / (m ^ 2 + n ^ 2)) ^ 2 = 1 :=
  by
  have : m ^ 2 + n ^ 2 ≠ 0
  · contrapose! hmn
    have hm : m = 0 := by nlinarith
    have hn : n = 0 := by nlinarith
    simp [hm, hn]
  field_simp
  ring

/-
In the following problem we prove that if :math:`x` is a primitive fifth root of unity, then
:math:`x+1/x` satisfies the quadratic equation

.. math::

    (x + 1/x) ^ 2 + (x + 1/x) - 1 = 0.

We have another use of contraposition in proving one of the nonzeroness hypotheses.  In the other,
we assume the goal did equal zero, and deduce a numeric contradiction with ``norm_num``.
Click through each invocation of ``polyrith`` to see what it gives you.

-/
example {x : ℂ} (hx : x ^ 5 = 1) (hx' : x ≠ 1) : (x + 1 / x) ^ 2 + (x + 1 / x) - 1 = 0 :=
  by
  have : x ≠ 0 := by
    intro h₀
    have : (1 : ℂ) = 0
    · polyrith
    norm_num at this
  field_simp
  have h₁ : x - 1 ≠ 0
  · contrapose! hx'
    polyrith
  apply mul_left_cancel₀ h₁
  polyrith
/-
Here is an exercise. Let :math:`ϕ:\mathbb{R}\to \mathbb{R}` be the function

.. math::

    ϕ(x)=\frac{1}{1-x}.

Away from the bad inputs :math:`x=0,1`, show that the triple composition of this function is the
identity.
-/
noncomputable def ϕ : ℝ → ℝ := fun x => (1 - x)⁻¹

example {x : ℝ} (h₁ : x ≠ 1) (h₀ : x ≠ 0) : ϕ (ϕ (ϕ x)) = x :=
  by
  dsimp [ϕ]
  sorry

/-
.. Sphere:

Stereographic projection
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In this section we construct stereographic projection as a bijection between the unit circle (minus
its north pole) and the real line.  The formulas for both directions of the bijection are
fractions, so we will use ``field_simp`` repeatedly.

We introduce the notation ``𝕊`` for the unit circle in ``ℝ × ℝ``, defined as the set of points
:math:`(x,y)` such that :math:`x^2+y^2=1`.

The forward direction of the bijection is the map

.. math::

  (x,y) \mapsto \frac{2x}{1-y}.

-/


namespace StereoExample  -- needed to prevent clashes with the definition in mathlib!

-- introduce notation for the circle
local notation "𝕊" => {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 1}

/-- Stereographic projection, forward direction. This is a map from `ℝ × ℝ` to `ℝ`. It is smooth
away from the horizontal line `p.2 = 1`.  It restricts on the unit circle to the stereographic
projection. -/
def stereoToFun (p : 𝕊) : ℝ :=
  2 * p.1.1 / (1 - p.1.2)

@[simp]
theorem stereoToFun_apply (p : 𝕊) : stereoToFun p = 2 * p.1.1 / (1 - p.1.2) := rfl

/-
The backward direction of the bijection is the map

.. math::

  w \mapsto \frac{1}{w^2+4}\left(4w, w ^ 2 - 4\right).

Here we encounter our first proof obligation. We want to prove this is well-defined as a map from
:math:`\mathbb{R}` to the circle, so we must prove that the norm-square of this expression is 1.
Fill in the proof below, using ``field_simp`` and a justification that the denominator is nonzero.
-/
/-- Stereographic projection, reverse direction.  This is a map from `ℝ` to the unit circle `𝕊` in
`ℝ × ℝ`. -/
def stereoInvFun (w : ℝ) : 𝕊 :=
  ⟨(w ^ 2 + 4)⁻¹ • (4 * w, w ^ 2 - 4), by
    dsimp
    sorry⟩




@[simp]
theorem stereoInvFun_apply (w : ℝ) :
    (stereoInvFun w : ℝ × ℝ) = (w ^ 2 + 4)⁻¹ • (4 * w, w ^ 2 - 4) :=
  rfl

/-
And in fact, since the bijection is going to be a map from :math:`\mathbb{R}` to the circle
*minus the north pole*, we must also prove that this expression is not equal to :math:`(0,1)`.
Fill in the proof below, using ``field_simp`` and a justification that the denominator is nonzero
to simplify the expression ``h``.  Then find a contradiction.
-/


open Subtype

theorem stereoInvFun_ne_north_pole (w : ℝ) : stereoInvFun w ≠ (⟨(0, 1), by simp⟩ : 𝕊) := by
  dsimp
  rw [Subtype.ext_iff, Prod.mk.inj_iff]
  dsimp
  intro h
  sorry

/-
Now comes the hardest part, proving that the given expression is a left inverse for the forward
direction.  The denominators that appear are complicated, and you may have quite a bit of work in
proving them nonzero.
-/

theorem stereo_left_inv {p : 𝕊} (hp : (p : ℝ × ℝ) ≠ (0, 1)) : stereoInvFun (stereoToFun p) = p := by
  ext1
  obtain ⟨⟨x, y⟩, pythag⟩ := p
  dsimp at pythag hp ⊢
  rw [Prod.mk.inj_iff] at hp ⊢
  have ha : 1 - y ≠ 0
  · sorry
  constructor
  · sorry
  · sorry

/-
The right inverse proof is much easier, only one denominator and we've seen it before.
-/

theorem stereo_right_inv (w : ℝ) : stereoToFun (stereoInvFun w) = w := by
  dsimp
  sorry

/-
Putting all these facts together with a bit of Lean abstract nonsense gives the bijection.
-/

/-- Stereographic projection, as a bijection to `ℝ` from the complement of `(0, 1)` in the unit
circle `𝕊` in `ℝ × ℝ`. -/
def stereographicProjection : ({(⟨(0, 1), by simp⟩ : 𝕊)}ᶜ : Set 𝕊) ≃ ℝ
    where
  toFun := stereoToFun ∘ (·)
  invFun w := ⟨stereoInvFun w, stereoInvFun_ne_north_pole w⟩
  left_inv p := by
    apply Subtype.ext
    apply stereo_left_inv
    simpa [Subtype.ext_iff] using p.prop
  right_inv w := stereo_right_inv w

end StereoExample

/-
.. Catalan:

A binomial coefficient identity
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In this section we prove the following identity involving binomial coefficients:

.. admonition:: Proposition

    For all natural numbers :math:`i` and :math:`j`,

    .. math::

        &\frac{i - j + 1}{2 (i + j + 1) (i + j + 2)} {2(i+1) \choose i+1} {2j\choose j}
        -
        \frac{i - j - 1}{2 (i +  j + 1) (i + j + 2)} {2i \choose i} {2 (j + 1) \choose j + 1} \\
        &=
        \frac{ 1}{(i + 1)(j + 1)} { 2i \choose i}{ 2j \choose j}.

This identity can be discovered by applying the "Gosper algorithm" to the right-hand side.  It
turns up in mathlib in the
`proof <https://leanprover-community.github.io/mathlib_docs/find/catalan_eq_central_binom_div/src>`_
that the recursive definition of the Catalan numbers  agrees with the definition by binomial
coefficients.

The "central binomial coefficient" expressions :math:`{2n \choose n}` are available in mathlib
under the name
-/

#check Nat.centralBinom
-- nat.central_binom : ℕ → ℕ

/-
and the following easy identity, relating successive central binomial coefficients, is available
in mathlib under the name ``nat.succ_mul_central_binom_succ``.

.. admonition:: Lemma

    For all natural numbers :math:`n`,

    .. math::

      (n + 1){2(n+1)\choose n+1} = 2 (2 n + 1) {2n \choose n}.

-/
#check Nat.succ_mul_centralBinom_succ

/-

The technique of the proof is pretty clear.  One should invoke the above lemma twice, once to turn
all :math:`{2(i+1)\choose i+1}`  into :math:`{2i\choose i}` and once to turn all
:math:`{2(j+1)\choose j+1}` into :math:`{2j\choose j}`.  We should therefore first state these two
applications of the lemma, then use ``field_simp`` to clear denominators and then ``polyrith`` to
figure out the coefficients with which to combine them.  ``field_simp`` will require proofs that
all the denominators we want to clear are nonzero, but this is easy since they are all of the form
"natural number plus one":
-/
#check Nat.succ_ne_zero

-- nat.succ_ne_zero : ∀ (n : ℕ), n.succ ≠ 0
/-
There is one main complication.  The lemmas ``nat.succ_mul_central_binom_succ`` and
``nat.succ_ne_zero`` concern natural numbers, whereas our goal (which involves divisions) is stated
as an equality of rational numbers.  So each of the applications of the above lemmas will need to
be cast -- try using `` exact_mod_cast`` or a combination of ``norm_cast`` and ``exact`` for this.

-/

example {i j : ℕ} :
    ((i + 1).centralBinom : ℚ) * j.centralBinom * (i - j + 1) / (2 * (i + j + 1) * (i + j + 2)) -
        i.centralBinom * (j + 1).centralBinom * (i - j - 1) / (2 * (i + j + 1) * (i + j + 2)) =
      i.centralBinom / (i + 1) * (j.centralBinom / (j + 1)) := by
  have h₁ : ((i : ℚ) + 1) * (i + 1).centralBinom = 2 * (2 * i + 1) * i.centralBinom
  · sorry
  have h₂ : ((j : ℚ) + 1) * (j + 1).centralBinom = 2 * (2 * j + 1) * j.centralBinom
  · sorry
  have : (i : ℚ) + j + 1 ≠ 0
  · sorry
  have : (i : ℚ) + j + 2 ≠ 0
  · sorry
  have : (i : ℚ) + 1 ≠ 0
  · sorry
  have : (j : ℚ) + 1 ≠ 0
  · sorry
  sorry
