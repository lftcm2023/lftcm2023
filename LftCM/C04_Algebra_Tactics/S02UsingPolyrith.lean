/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth, Marc Masdeu
-/
import LftCM.Common
import LftCM.Attr
import Mathlib.Data.Polynomial.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Polyrith
import Mathlib.Analysis.Quaternion
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GroupPower.Ring


local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue #2220

noncomputable section
open Polynomial Complex Quaternion
open scoped ComplexConjugate Quaternion

/-! This file contains a lot of computationally-intensive evaluation of operations on the complex
numbers, matrices and quaternions.
We speed it up slightly by specifiying in advance the path the simplifier should take.
-/
attribute [complex_simps] normSq_eq_conj_mul_self norm_eq_abs ofReal_pow ofReal_one
  map_sub map_one conj_neg_I
attribute [quaternion_simps] Matrix.head_cons Matrix.cons_vec_bit0_eq_alt0 Matrix.cons_val_zero
  Matrix.cons_val_one Matrix.cons_vecAppend Matrix.cons_vecAlt0 Matrix.cons_val' Matrix.empty_val'
  Matrix.empty_vecAlt0 Matrix.empty_vecAppend Matrix.one_apply_eq Matrix.one_apply_ne
  MulZeroClass.zero_mul one_pow add_zero eq_self_iff_true MulZeroClass.mul_zero zero_pow' tsub_zero
  Matrix.vecHead Matrix.vecTail Matrix.cons_mul Matrix.cons_vecMul
  Matrix.cons_val_zero Matrix.cons_val_one Matrix.empty_vecMul Matrix.empty_vecAppend
  Matrix.empty_mul Matrix.one_apply_eq Matrix.one_apply_ne Matrix.conjTranspose_apply
  Matrix.head_cons Matrix.one_fin_three Matrix.mul_apply Fin.sum_univ_succ
  Quaternion.one_re Quaternion.one_imI Quaternion.one_imJ Quaternion.one_imK
  Quaternion.neg_re Quaternion.neg_imI Quaternion.neg_imJ Quaternion.neg_imK
  MonoidHom.mem_mker Set.mem_insert_iff Set.mem_singleton_iff Matrix.one_apply_eq
  Subtype.ext_iff Subtype.coe_mk SetLike.mem_coe
  Pi.add_apply Pi.smul_apply Pi.zero_apply
  Fin.succ_zero_eq_one Fin.succ_one_eq_two
  QuaternionAlgebra.ext_iff Set.mem_insert_iff Set.mem_singleton_iff
  IsROrC.star_def IsROrC.conj_to_real Algebra.id.smul_eq_mul Submonoid.coe_one neg_zero
  Function.comp_apply Quaternion.coe_one Quaternion.coe_zero
  Quaternion.ext_iff zero_mul

/-

.. Chebyshev:

Using polyrith
------------------

Chebyshev polynomials
^^^^^^^^^^^^^^^^^^^^^^

The Chebyshev polynomials (of the first kind) are a sequence of polynomials :math:`T_n(x)` defined
recursively:

.. math::

    \begin{cases}
    T_0(x)&=1\\
    T_1(x)&=x\\
    \text{for $n\in\mathbb{N}$, } T_{n+2}(x)&=2xT_{n+1}(x)-T_n(x).
    \end{cases}

So :math:`T_2(x)=2x^2-1`, :math:`T_3(x)=4x^3-3x`, etc.

We express the sequence of Chebyshev polynomials in Lean as a function from the natural numbers
``ℕ`` to the integer-coefficient polynomials ``ℤ[X]``, defined recursively.
-/

/-- The Chebyshev polynomials, defined recursively.-/
noncomputable def T : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => 2 * X * T (n + 1) - T n

-- now record the three pieces of the recursive definition for easy access
theorem T_zero : T 0 = 1 := rfl

theorem T_one : T 1 = X := rfl

theorem T_add_two (n : ℕ) : T (n + 2) = 2 * X * T (n + 1) - T n := by rw [T]

/-
In this section we will prove the multiplication formula for Chebyshev polynomials:

.. admonition:: Theorem

    For all natural numbers :math:`m` and :math:`k`,

    .. math::

        2 T_m(x)T_{m+k}(x) = T_{2m+k}(x)+T_k(x).

This is proved by induction on :math:`m`: if the formula is true for :math:`m`
and :math:`m+1` (for all :math:`k`), then it is true for :math:`m+2` (for all :math:`k`). I leave
the two base cases as exercises. Here is the paper proof of the inductive step:

.. math::

    2T_{m+2}T_{(m+2)+k}
    &=2\left(2xT_{m+1}-T_m\right)T_{m+k+2}\\
    &=2x\left(2T_{m+1}T_{(m+1)+(k+1)}\right)-2T_mT_{m+(k+2)}\\
    &=2x\left(T_{2(m+1)+(k+1)}+T_{k+1}\right)-\left(T_{2m+(k+2)}+T_{k+2}\right)\\
    &=\left(2xT_{2m+k+3}-T_{2m+k+2}\right)+\left(2xT_{k+1}-T_{k+2}\right)\\
    &=T_{2(m+2)+k}+T_{k}.

Notice that two facts are being invoked (each repeatedly) during this proof: the recurrence
relation, in Lean ``T_add_two``, and the inductive hypothesis of the theorem, which within the
proof below will carry the same name, ``mul_T``, as the theorem itself.  To make ``polyrith`` do
this proof you should determine precisely which input values these facts are being used with in the
above proof, and state them in Lean with those input values.  See the broken proof below for the
basic idea.

There is one subtlety. It will happen that the same natural number appears as the index of the
sequence `T`, but in more than one way.  For example, in the setup below, both ``m + 37`` and
``37 + m`` appear as indices.  This prevents ``polyrith`` from parsing ``T (m + 37)`` and
``T (37 + m)`` as the same token.  So, before running ``polyrith``, normalize all indices by
running ``ring_nf`` ("ring normal form") simultaneously on all the hypotheses you care about and on
the goal.
-/

/-- The product of two Chebyshev polynomials is the sum of two other Chebyshev polynomials. -/
theorem mul_T : ∀ m : ℕ, ∀ k, 2 * T m * T (m + k) = T (2 * m + k) + T k
  | 0 => by
    sorry
  | 1 => by
    sorry
  | m + 2 => by
    intro k
    have H₁ := mul_T (m + 37) (k * 37) -- not actually a relevant pair of input values!
    have h₁ := T_add_two 7 -- not actually a relevant input value!
    have h₂ := T_add_two (37 + m) -- not actually a relevant input value!
    ring_nf at H₁ h₁ h₂ ⊢
    sorry -- polyrith should work if you have added the relevant hypotheses (may be more than 3)


/-

.. IsometryPlane:

Isometries of the complex plane
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Let us identify the Euclidean plane with the complex numbers :math:`\mathbb{C}`.  In this section
we prove the following lemma:

.. admonition:: Lemma

    If :math:`f:\mathbb{C}\to\mathbb{C}` is a
    **real-linear** isometry of the plane fixing :math:`1`, then :math:`f(i)` is either :math:`i`
    or :math:`-i`.

This lemma
`appears in mathlib <https://leanprover-community.github.io/mathlib_docs/find/linear_isometry_complex_aux/src>`_
in the proof of the classical theorem that isometries :math:`f:\mathbb{C}\to\mathbb{C}` of the
plane are of the two forms

.. math::

    f(z)=az+b,\qquad f(z)=a\overline{z}+b

for :math:`a,b\in\mathbb{C}` with :math:`|a|=1`: compositions of a translation, a rotation, and
(possibly) a reflection.  (An isometry has to be affine; by postcomposition with a translation we
can arrange that :math:`f(0)=0`, i.e. :math:`f` is linear; by postcomposition with a rotation we
can arrange that :math:`f(1)=1`, and then after the above lemma :math:`f` is determined on the real
basis :math:`\{1, i\}` for :math:`\mathbb{C}`, hence everywhere by linearity.


Real-linear isometries from :math:`\mathbb{C}` to :math:`\mathbb{C}` are expressed in
Lean by the type ``ℂ →ₗᵢ[ℝ] ℂ``.  The ``ₗᵢ`` subscript stands
for "linear isometry", and the ``[ℝ]`` denotes the scalar field to consider for the linearity.

The lemma is proved on paper as follows.  Since :math:`f` is linear and norm-preserving and
:math:`f(1)=1`, we have

.. math::

    f(i)\overline{f(i)}&=|f(i)|^2\\
      &=|i|^2\\
      &=i\overline{i},\\
    \left(f(i)-1\right)\left(\overline{f(i)} - 1\right)
      &=\left(f(i)-f(1)\right)\left(\overline{f(i)} - \overline{f(1)}\right)\\
      &=f(i-1)\overline{f(i - 1)}\\
      &=|f(i-1)|^2\\
      &=|i-1|^2\\
      &=(i-1)(\overline{i}-1).

.. admonition:: Exercise

    Deduce from these two facts that

    .. math::

        \left(f(i) - i\right)\left(\overline{f(i)}-\overline{-i}\right) = 0.

    (Hint: Subtract and factor.)

This fixes :math:`f(i)` as either :math:`i` (if the left factor vanishes) or :math:`-i` (if the
right factor vanishes).

We present the skeleton of this argument in Lean below, with the exercise indicated above left as a
sorry.  A tricky point is that ``linear_combination``/``polyrith``
does not know facts specific to the ring of complex numbers, such as that :math:`i^2=-1` or that
:math:`\overline{i}=-i`.  You can state any needed such facts explicitly and prove them using
``norm_num`` (of course, there are lemmas for this, but why bother memorizing them?).  Then you can
rewrite by these facts, or just include them in the context for ``polyrith`` to pick up.
-/
example {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) : f I = I ∨ f I = -I :=
  by
  have key : (f I - I) * (conj (f I) - conj (-I)) = 0
  · sorry
  cases' eq_zero_or_eq_zero_of_mul_eq_zero key with hI hI
  · sorry
  · sorry


/-
.. DoubleCover:

Double cover of SO(3, ℝ)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In this section we construct the double cover of :math:`SO(3,\mathbb{R})` by the unit quaternions.
We first state the formula which will describe this double cover as a map from the quaternions
:math:`\mathbb{H}` to the 3 × 3 matrices. It sends the quaternion :math:`x+iy+jz+wk` to

.. math::

    \begin{pmatrix}
    x ^ 2 + y ^ 2 - z ^ 2 - w ^ 2 & 2  (y z - w x) & 2 (y w + z x) \\
    2 (y z + w x) &   x ^ 2 + z ^ 2 - y ^ 2 - w ^ 2 & 2 (z w - y x) \\
    2 (y w - z x) &  2 (z w + y x) & x ^ 2 + w ^ 2 - y ^ 2 - z ^ 2
    \end{pmatrix}.
-/
/-- Explicit matrix formula for the double cover of SO(3, ℝ) by the unit quaternions. -/
@[quaternion_simps]
def Quaternion.toMatrix (a : ℍ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let ⟨x, y, z, w⟩ := a
  ![![x ^ 2 + y ^ 2 - z ^ 2 - w ^ 2, 2 * (y * z - w * x), 2 * (y * w + z * x)],
    ![2 * (y * z + w * x), x ^ 2 + z ^ 2 - y ^ 2 - w ^ 2, 2 * (z * w - y * x)],
    ![2 * (y * w - z * x), 2 * (z * w + y * x), x ^ 2 + w ^ 2 - y ^ 2 - z ^ 2]]

attribute [quaternion_simps] Matrix.head_cons Matrix.cons_vec_bit0_eq_alt0 Matrix.cons_val_zero
  Matrix.cons_val_one Matrix.cons_vecAppend Matrix.cons_vecAlt0 Matrix.cons_val' Matrix.empty_val'
  Matrix.empty_vecAlt0 Matrix.empty_vecAppend Matrix.one_apply_eq Matrix.one_apply_ne
  MulZeroClass.zero_mul one_pow add_zero eq_self_iff_true MulZeroClass.mul_zero zero_pow' tsub_zero
  Matrix.vecHead Matrix.vecTail Matrix.cons_mul Matrix.cons_vecMul
  Matrix.cons_val_zero Matrix.cons_val_one Matrix.empty_vecMul Matrix.empty_vecAppend
  Matrix.empty_mul Matrix.one_apply_eq Matrix.one_apply_ne Matrix.conjTranspose_apply
  Matrix.head_cons Matrix.one_fin_three Matrix.mul_apply Fin.sum_univ_succ
  Quaternion.one_re Quaternion.one_imI Quaternion.one_imJ Quaternion.one_imK
  Quaternion.neg_re Quaternion.neg_imI Quaternion.neg_imJ Quaternion.neg_imK
  MonoidHom.mem_mker Set.mem_insert_iff Set.mem_singleton_iff Matrix.one_apply_eq
  Subtype.ext_iff Subtype.coe_mk SetLike.mem_coe
  Pi.add_apply Pi.smul_apply Pi.zero_apply
  Fin.succ_zero_eq_one Fin.succ_one_eq_two
  QuaternionAlgebra.ext_iff
  Quaternion.toMatrix Set.mem_insert_iff Set.mem_singleton_iff
  IsROrC.star_def IsROrC.conj_to_real Algebra.id.smul_eq_mul Submonoid.coe_one neg_zero
  Function.comp_apply Quaternion.coe_one Quaternion.coe_zero
  Quaternion.ext_iff zero_mul

/-
This turns out to be a "homomorphism of monoids", denoted in Lean by ``→*``; that is, it preserves
multiplication and the identity.  Here is what the proof of that fact looks like.  It would be
extremely tedious on paper, but it's very fast in Lean, because it simply requires checking
coefficient-wise  :math:`9=3 \times 3` identities of real-number expressions (for the preservation
of the identity element) and 9 identities of polynomials (for the preservation of multiplication).
-/
/-- The explicit matrix formula `to_matrix` defines a monoid homomorphism from the quaternions into
the algebra of 3x3 matrices. -/
@[quaternion_simps] def Quaternion.toMatrixHom' : ℍ →* Matrix (Fin 3) (Fin 3) ℝ
    where
  toFun := Quaternion.toMatrix
  map_one' :=
    show Quaternion.toMatrix ⟨1, 0, 0, 0⟩ = 1 by
      ext (i j); fin_cases i <;> fin_cases j <;>
        simp [quaternion_simps]
  map_mul' := by
    rintro ⟨x, y, z, w⟩ ⟨r, s, t, u⟩
    show Quaternion.toMatrix ⟨_, _, _, _⟩
      = Quaternion.toMatrix ⟨_, _, _, _⟩ * Quaternion.toMatrix ⟨_, _, _, _⟩
    ext (i j); fin_cases i <;> fin_cases j <;> (simp [quaternion_simps]; ring)

/-
Now we write down a definition of the *unit* quaternions.  We give it the abstract-nonsense
definition as the ``mker`` (for "monoid kernel") of the "norm_square" monoid homomorphism
``quaternion.norm_sq`` from the quaternions to the reals; this already existed in mathlib. Then we
prove a quick lemma that this is equivalent to the pedestrian definition, the sums of the squares
of the four components summing to 1.
-/
/-- The group (we only prove it to be a monoid) of unit quaternions. -/
def unitQuaternions : Submonoid ℍ :=
  MonoidHom.mker ((Quaternion.normSq : ℍ →*₀ ℝ) : ℍ →* ℝ)

@[simp high] theorem mem_unitQuaternions (a : ℍ) :
    a ∈ unitQuaternions ↔ a.re ^ 2 + a.imI ^ 2 + a.imJ ^ 2 + a.imK ^ 2 = 1 := by
  simp [←Quaternion.normSq_def']
  exact Iff.rfl

/-
We prove that the unit quaternions form a group, although we will not need it later.
-/
/-- The group of unit quaternions. -/
def unitQuaternions' : Subgroup (Units ℍ) where
  toSubmonoid := {
    carrier := {x | x.val ∈ unitQuaternions}
    mul_mem' := by
      sorry
    one_mem' := by
      sorry
  }
  inv_mem' := by
    rintro ⟨a, b, h, h'⟩
    intro H
    simp at H ⊢
    sorry -- use Quaternion.mul_* lemmas


/-
The 3 × 3 orthogonal group is available in mathlib already, as a submonoid of the 3 x 3
matrices. (Exercise for the reader: the monoid structure is in mathlib but no one seems yet to have
proved it's a *group*, i.e. closed under inversion.)
-/
#check Matrix.orthogonalGroup (Fin 3) ℝ

-- matrix.orthogonal_group ℝ : submonoid (matrix (fin 3) (fin 3) ℝ)
namespace unitQuaternions

open Quaternion

/-
The first serious calculation is to prove that the matrix formula stated above is well-defined as a
map from the unit quaternions to :math:`SO(3,\mathbb{R})`.  That is, we have to prove that if
:math:`x+iy+jz+kw` is a unit quaternion then the formula produces an element of
:math:`SO(3,\mathbb{R})`.

To prove this, we have to multiply it by its transpose, obtaining a 3 × 3 matrix of quartic
polynomials in :math:`x,y,z,w`, and check entry by entry that if :math:`x^2+y^2+z^2+w^2=1` then
that quartic polynomial is one (respectively, zero) on (respectively, off) the diagonal.

All these 9 checks can be done by ``polyrith``.  Click through in your Lean file to see the proofs
that ``polyrith`` comes up with for each one.
-/
/-- The explicit matrix formula `to_matrix` sends a unit quaternion to an element of SO(3, ℝ). -/
theorem toMatrix_mem_orthogonal {a : ℍ} (ha : a ∈ unitQuaternions) :
    toMatrix a ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
  by
  rw [Matrix.mem_orthogonalGroup_iff]
  cases' a with x y z w
  have H : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 1 := by rwa [mem_unitQuaternions] at ha
  ext (i j)
  fin_cases i <;> fin_cases j <;> simp [quaternion_simps]
  · polyrith
  · polyrith
  · polyrith
  · polyrith
  · polyrith
  · polyrith
  · polyrith
  · polyrith
  · polyrith

/-- Double cover of SO(3, ℝ) by the unit quaternions, as a homomorphism of monoids. This is obtained
by restriction of the homomorphism `quaternion.to_matrix_hom'` from `ℍ` into the 3x3 matrices; it is
well-defined by `to_matrix_mem_orthogonal`. -/
@[quaternion_simps]
def toMatrixHom : unitQuaternions →* Matrix.orthogonalGroup (Fin 3) ℝ :=
  (toMatrixHom'.restrict unitQuaternions).codRestrict (Matrix.orthogonalGroup (Fin 3) ℝ) fun a =>
    toMatrix_mem_orthogonal a.prop

/-
So the monoid homomorphism from :math:`\mathbb{H}` to 3 × 3 matrices descends to a homomorphism
``unit_quaternions.to_matrix_hom`` from the unit quaternions to :math:`SO(3, \mathbb{R})`, with a
couple more lines of abstract nonsense.

We now want to show that this homomorphism is a *double cover*; that is, its kernel has two
elements, :math:`\{1, -1\}`.

There are two directions to this proof.  The easy direction is that both these elements are in the
kernel; this is a numeric check that can be done with 2 × 3 × 3 applications of ``norm_num``.  The
hard direction is that an element of the kernel is one of these two.

So let :math:`x+iy+jz+kw` be an element of the kernel.  We have that :math:`x^2+y^2+z^2+w^2=1`,
since it is a unit quaternion, and we also have 9 further quadratic equations available about
:math:`x,y,z,w`: for example, by looking at the second row and first column in the matrix (in Lean
this is the first row and zero-th column!) we have that :math:`2(y z + w  x)=0`.

We will use ``polyrith`` to deduce that :math:`y=0`, :math:`z=0`, :math:`w=0`,  and :math:`x^2=1`,
which lets us conclude that :math:`x+iy+jz+kw = \pm 1 + 0i+0j+0k` as desired.

The proof below is on the right track, but it is broken: I have not given ``polyrith`` all the
information it needs.  (I was lazy and just wrote out the result of checking the (0,1)-th
coefficient of the matrix, as discussed above.)  Figure out what further matrix coefficients to
check so that ``polyrith`` has all the information it needs.  Or just write down all nine!
-/
/-- The unit quaternion -1 (the quaternion -1 together with a proof that its norm is one). -/
@[quaternion_simps]
noncomputable def negOne : unitQuaternions :=
  ⟨-1, show (⟨_, _, _, _⟩ : ℍ) ∈ _ by
    rw [mem_unitQuaternions]
    norm_num ⟩

@[quaternion_simps]
theorem coe_negOne : (negOne : ℍ) = -1 := rfl


/-- Verify the "double cover" property of the homomorphism from unit quaternions to SO(3, ℝ): the
kernel is {1, -1}. -/
theorem toMatrixHom_mker : (MonoidHom.mker toMatrixHom : Set unitQuaternions) = {1, negOne} := by
  ext a
  obtain ⟨⟨x, y, z, w⟩, h⟩ := a
  have H : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 1 := by rwa [mem_unitQuaternions] at h

  simp [quaternion_simps]

  constructor
  -- hard direction: a quaternion in the kernel is ±1
  · intro h1
    have h₀₀ := congr_fun₂ h1 0 0
    -- Add more matrix entry inspections here as needed, and adjust the simplification line.
    -- The `polyrith` applications that follow will be broken until you do this!
    simp [quaternion_simps] at h₀₀
    norm_num at h1 h₀₀
    have hy : y = 0
    · polyrith
    have hz : z = 0
    · polyrith
    have hw : w = 0
    · polyrith
    have hx : x ^ 2 = (1 : ℝ) ^ 2
    · polyrith
    -- now do a case division depending on the two cases for `x ^ 2 = 1 ^ 2`
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hx
    cases' hx with hx hx
    · simp [hx, hy, hz, hw]
    · simp [hx, hy, hz, hw]
  -- easy direction: ±1 are in the kernel
  rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> (ext (i j); fin_cases i <;> fin_cases j) <;>
  simp [quaternion_simps]

end unitQuaternions
