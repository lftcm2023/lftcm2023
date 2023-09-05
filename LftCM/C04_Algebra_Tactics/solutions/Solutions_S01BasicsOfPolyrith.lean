/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import LftCM.Common
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Polyrith
/-
.. LinearCombination:

Basics
-----------


Basics of the linear_combination tactic
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

How do you do algebra in Lean?  Let's consider a concrete problem.

.. admonition:: Problem

    Let :math:`a` and :math:`b` be complex numbers and suppose that :math:`a - 5b = 4` and
    :math:`b + 2 = 3`. Show that :math:`a = 9`.

One way to solve this on paper is by a "calculation block", and this translates directly, if
painstakingly, to Lean.

.. math::

    a & = (a - 5 b) + 5  b \\
    & = 4 + 5  b \\
    & = -6 + 5 (b + 2) \\
    & = -6 + 5 \cdot 3 \\
    & = 9.

-/

example {a b : ℂ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 :=
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * b := by rw [h₁]
    _ = -6 + 5 * (b + 2) := by ring
    _ = -6 + 5 * 3 := by rw [h₂]
    _ = 9 := by ring

/-
Implicitly, when we write a calculation like this on paper, we tend to alternate "rearrangement
steps" (done in Lean with ``ring``) and "substitution steps" (done in Lean with ``rw``).

Another method: You might be familiar with the ``linarith`` tactic, for deducing implications among
linear inequalities.  If we were working over a linear ordered field such as :math:`\mathbb{R}` or
:math:`\mathbb{Q}`, this tactic would be a great way to solve this problem.
-/

example {a b : ℝ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 := by linarith

/-
But over  :math:`\mathbb{C}`, which has no order, we could only invoke ``linarith`` by first taking
real and imaginary parts of both sides -- and over a general field this wouldn't work at all.

In this section we will introduce a tactic, ``linear_combination``, which is well-adapted to
algebra over general commutative rings. Here is how our example is solved using
``linear_combination``.
-/

example {a b : ℂ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 := by linear_combination h₁ + 5 * h₂

/-
The tactic ``linear_combination`` works by finding coefficients with which LHS - RHS of the goal is
a linear combination of LHS - RHS of the hypotheses.  Here LHS - RHS of ``h₁`` is :math:`a-5b-4`,
LHS - RHS of ``h₂`` is :math:`b-1`, and LHS - RHS of the goal is :math:`a-9`.  It is indeed true
that

.. math::

    a - 9 = (a - 5b - 4) + 5 (b - 1).

``linear_combination`` is a great tactic to use when your intuition for a problem is to "add
something to both sides" or "divide both sides by something" or "add two equations".

.. admonition:: Problem

    Let :math:`m` and :math:`n` be integers and suppose that :math:`m - n = 0`. Show that
    :math:`m = n`.


-/

example {m n : ℤ} (h : m - n = 0) : m = n := by linear_combination h

/-

.. admonition:: Problem

    Let :math:`K` be a field of characteristic zero, let :math:`s\in K`, and suppose that
    :math:`3s+1 = 4`. Show that :math:`s = 1`.

-/

example {K : Type _} [Field K] [CharZero K] {s : K} (hs : 3 * s + 1 = 4) : s = 1 := by
  linear_combination 1 / 3 * hs


/-

.. admonition:: Problem

    Let :math:`p` and :math:`q` be complex numbers and suppose that :math:`p+2q=4` and
    :math:`p-2q=2`. Show that :math:`2p = 6`.


-/

example {p q : ℂ} (h₁ : p + 2 * q = 4) (h₂ : p - 2 * q = 2) : 2 * p = 6 := by
  linear_combination h₁ + h₂


/-

Here are a *lot* of exercises.  Do them until you get bored, then go on to the next section.

-/


example {x y : ℤ} (h₁ : 2 * x + y = 4) (h₂ : x + y = 1) : x = 3 := by
  linear_combination h₁ - h₂

example {r s : ℝ} (h₁ : r + 2 * s = -1) (h₂ : s = 3) : r = -7 := by
  linear_combination h₁ - 2 * h₂

example {c : ℚ} (h₁ : 4 * c + 1 = 3 * c - 2) : c = -3 := by
  linear_combination h₁

example {x y : ℤ} (h₁ : x - 3 * y = 5) (h₂ : y = 3) : x = 14 := by
  linear_combination h₁ + 3 * h₂

example {x y : ℤ} (h₁ : 2 * x - y = 4) (h₂ : y - x + 1 = 2) : x = 5 := by
  linear_combination h₁ + h₂

example {x y : ℝ} (h₁ : x = 3) (h₂ : y = 4 * x - 3) : y = 9 := by
  linear_combination 4 * h₁ + h₂

example {a b c : ℝ} (h₁ : a + 2 * b + 3 * c = 7) (h₂ : b + 2 * c = 3) (h₃ : c = 1) : a = 2 := by
  linear_combination h₁ - 2 * h₂ + h₃

example {a b : ℝ} (h₁ : a + 2 * b = 4) (h₂ : a - b = 1) : a = 2 := by
  linear_combination 1 / 3 * h₁ + 2 / 3 * h₂

example {u v : ℚ} (h₁ : u + 2 * v = 4) (h₂ : u - 2 * v = 6) : u = 5 := by
  linear_combination 1 / 2 * h₁ + 1 / 2 * h₂

example {u v : ℚ} (h₁ : 4 * u + v = 3) (h₂ : v = 2) : u = 1 / 4 := by
  linear_combination 1 / 4 * h₁ - 1 / 4 * h₂
  -- BOTH:



/-
.. NonlinearExamples:

linear_combination for nonlinear equations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Despite the name, where ``linear_combination`` really comes into its own is in solving *nonlinear*
equations: polynomial equations of degree greater than one. For example, consider the following
calculation, which comes up in studying the twisted cubic.


.. admonition:: Problem

    Let :math:`x, y, z, w` be complex numbers and suppose that :math:`xz=y^2` and :math:`yw=z^2`.
    Show that :math:`z(xw-yz)=0`.

This can be solved by exhibiting :math:`z(xw-yz)` as an element of the ideal generated by
:math:`xz-y^2` and :math:`yw-z^2`:

.. math::

    z(xw-yz) = w (xz-y^2) + y (yw-z^2).

-/

example {x y z w : ℂ} (h₁ : x * z = y ^ 2) (h₂ : y * w = z ^ 2) : z * (x * w - y * z) = 0 := by
  linear_combination w * h₁ + y * h₂

/-
Even on a problem where your intuition is to use ``rw``, the tactic ``linear_combination`` can
probably do it.

.. admonition:: Problem

    Let :math:`a` and :math:`b` be rational numbers and suppose that :math:`a = b`.
    Show that :math:`a ^ 2 = b ^ 2`.

-/

example {a b : ℚ} (h : a = b) : a ^ 2 = b ^ 2 := by linear_combination (a + b) * h

/-
.. admonition:: Problem

    Let :math:`a` and :math:`b` be rational numbers and suppose that :math:`a = b`.
    Show that :math:`a ^ 3 = b ^ 3`.

-/

example {a b : ℚ} (h : a = b) : a ^ 3 = b ^ 3 := by linear_combination (a ^ 2 + a * b + b ^ 2) * h

/-
Do you see the pattern?

Importantly, ``linear_combination`` strictly subsumes the tactic ``ring``.  In fact, ``ring``
amounts to doing a ``linear_combination`` of no hypotheses!

.. admonition:: Problem

    Let :math:`m` and :math:`n` be integers.  Show that

    .. math::

      (m ^ 2 - n ^ 2) ^ 2 + (2  m n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2.

-/

example (m n : ℤ) : (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  linear_combination

/-
Try the following examples, until you get bored.

-/

example {x y : ℝ} (h₁ : x + 3 = 5) (h₂ : 2 * x - y * x = 0) : y = 2 := by
  linear_combination (-1 / 2 * y + 1) * h₁ - 1 / 2 * h₂

example {x y : ℝ} (h₁ : x - y = 4) (h₂ : x * y = 1) : (x + y) ^ 2 = 20 := by
  linear_combination (x - y + 4) * h₁ + 4 * h₂

example {a b c d e f : ℤ} (h₁ : a * d = b * c) (h₂ : c * f = d * e) : d * (a * f - b * e) = 0 := by
  linear_combination f * h₁ + b * h₂

example {u v : ℝ} (h₁ : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by
  linear_combination (u + v + 2) * h₁

example {z : ℝ} (h₁ : z ^ 2 + 1 = 0) : z ^ 4 + z ^ 3 + 2 * z ^ 2 + z + 3 = 2 := by
  linear_combination (z ^ 2 + z + 1) * h₁

example {p q r : ℚ} (h₁ : p + q + r = 0) (h₂ : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 := by
  linear_combination (p + q + r) * h₁ - 2 * h₂


/-
.. Polyrith:

Basics of the polyrith tactic
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Surprise!  None of the work we did in the last two sections finding the coefficients for
``linear_combination`` by hand was necessary.  A higher level tactic, ``polyrith``, contributed to
mathlib in July 2022 by Brown undergraduate Dhruv Bhatia, will obtain them from the Sage function
`MPolynomial_libsingular.lift <https://doc.sagemath.org/html/en/reference/polynomial_rings/sage/rings/polynomial/multi_polynomial_libsingular.html#sage.rings.polynomial.multi_polynomial_libsingular.MPolynomial_libsingular.lift>`_,
so long as you have an internet connection.

(The tactic also requires that your ``python3`` have the ``requests`` package installed.  This is
probably already the case, but if you encounter bugs that look like they might be caused by this,
install the package by running ``python3 -m pip install requests`` at the command line.)

Here is ``polyrith`` being let loose on all the examples from the previous two sections.  In each
case, click on the blue "Try this" underline, to replace the ``polyrith`` invocation (which will
query Sage each time) with an automatically-computed ``linear_combination`` which stores its result.

-/

example {a b : ℂ} (h₁ : a - 5 * b = 4) (h₂ : b + 2 = 3) : a = 9 := by
  linear_combination h₁ + 5 * h₂

example {m n : ℤ} (h : m - n = 0) : m = n := by
  linear_combination h

example {K : Type _} [Field K] [CharZero K] {s : K} (hs : 3 * s + 1 = 4) : s = 1 := by
  linear_combination hs / 3

example {p q : ℂ} (h₁ : p + 2 * q = 4) (h₂ : p - 2 * q = 2) : 2 * p = 6 := by
  linear_combination h₁ + h₂

example {x y z w : ℂ} (h₁ : x * z = y ^ 2) (h₂ : y * w = z ^ 2) : z * (x * w - y * z) = 0 := by
  linear_combination w * h₁ + y * h₂

example {a b : ℚ} (h : a = b) : a ^ 2 = b ^ 2 := by
  linear_combination (a + b) * h

example {a b : ℚ} (h : a = b) : a ^ 3 = b ^ 3 := by
  linear_combination (a ^ 2 + a * b + b ^ 2) * h

example (m n : ℤ) : (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  linear_combination
