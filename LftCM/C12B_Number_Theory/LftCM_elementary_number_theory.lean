/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : María Inés de Frutos-Fernández
-/

import Mathlib.Data.Int.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/- The first part of the talk is adapted from Section 6.3 of `Mathematics in Lean` (J. Avigad). -/

/-! GAUSSIAN INTEGERS. -/

/-- The Gaussian integers `ℤ[i]` are the set of complex numbers of the form
  `{ a + bi | a, b ∈ ℤ }`. -/
@[ext] structure gaussInt :=
  re : ℤ
  im : ℤ

--#check gaussInt.ext
--#check gaussInt.ext_iff

namespace gaussInt

-- We show that the Gaussian integers are a commutative ring.

-- (a + bi) + (c + di) = (a + c) + (b + d)i
instance : Add gaussInt  := ⟨λ x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg gaussInt  := ⟨λ x ↦ ⟨-x.re, -x.im⟩⟩
instance : Zero gaussInt := ⟨⟨0, 0⟩⟩

-- (a + bi) * (c + di) = (ad - bc) + (ad + bc)i
instance : Mul gaussInt  :=
⟨λ x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
instance : One gaussInt  := ⟨⟨1, 0⟩⟩

-- We provide lemmas for easily rewriting the above definitions.
lemma zero_def : (0 : gaussInt) = ⟨0, 0⟩ := rfl
lemma one_def : (1 : gaussInt) = ⟨1, 0⟩ := rfl
lemma add_def (x y : gaussInt) : x + y = ⟨x.re + y.re, x.im + y.im⟩ := rfl
lemma neg_def (x : gaussInt) : -x = ⟨-x.re, -x.im⟩ := rfl
lemma mul_def (x y : gaussInt) :
  x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ := rfl

-- Same for real and imaginary parts.
@[simp] lemma zero_re : (0 : gaussInt).re = 0 := rfl
@[simp] lemma zero_im : (0 : gaussInt).im = 0 := rfl
@[simp] lemma one_re : (1 : gaussInt).re = 1 := rfl
@[simp] lemma one_im : (1 : gaussInt).im = 0 := rfl
@[simp] lemma add_re (x y : gaussInt) : (x + y).re = x.re + y.re := rfl
@[simp] lemma add_im (x y : gaussInt) : (x + y).im = x.im + y.im := rfl
@[simp] lemma neg_re (x : gaussInt) : (-x).re = - x.re := rfl
@[simp] lemma neg_im (x : gaussInt) : (-x).im = - x.im := rfl
@[simp] lemma mul_re (x y : gaussInt) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] lemma mul_im (x y : gaussInt) : (x * y).im = x.re * y.im + x.im * y.re := rfl

lemma mk_def (x : gaussInt) :  x = ⟨x.re, x.im⟩ := by ext <;> rfl

-- The `comm_ring` structure on ℤ[i].
instance instCommRing : CommRing gaussInt where
  zero := 0
  one  := 1
  add  := (· + ·)
  neg  := λ x ↦ -x
  mul  := (· * ·)
  natCast := λ n ↦ ⟨n, 0⟩ -- Inclusion of ℕ in ℤ[i]
  intCast := λ n ↦ ⟨n, 0⟩ -- Inclusion of ℤ in ℤ[i]
  -- We check the commutative ring axioms.
  add_comm      := by
    intro a b
    ext <;> simp <;> ring
  add_assoc     := by intros; ext <;> simp <;> ring
  zero_add      := by intros; ext <;> simp
  add_zero      := by intros; ext <;> simp
  zero_mul      := by intros; ext <;> simp
  mul_zero      := by intros; ext <;> simp
  add_left_neg  := by intros; ext <;> simp
  mul_assoc     := by intros; ext <;> simp <;> ring
  one_mul       := by intros; ext <;> simp
  mul_one       := by intros; ext <;> simp
  left_distrib  := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  mul_comm      := by intros; ext <;> simp <;> ring

@[simp] lemma sub_re (x y : gaussInt) : (x - y).re = x.re - y.re := rfl

@[simp] lemma sub_im (x y : gaussInt) : (x - y).im = x.im - y.im := rfl

-- Some useful lemmas for the inclusions of ℤ and ℕ in ℤ[i].
lemma int_cast (x : ℤ) : (x : gaussInt) = ⟨x, 0⟩ := rfl
@[simp] lemma int_cast_re (n : ℤ) : (n : gaussInt).re = n := rfl
@[simp] lemma int_cast_im (n : ℤ) : (n : gaussInt).im = 0 := rfl
lemma int_cast_inj : Function.Injective (λ x : ℤ ↦ (x : gaussInt)) :=
λ x y hxy ↦ by simpa [int_cast] using hxy

lemma nat_cast (x : ℕ) : (x : gaussInt) = ⟨x, 0⟩ := rfl
@[simp] lemma nat_cast_re (n : ℕ) : (n : gaussInt).re = n := rfl
@[simp] lemma nat_cast_im (n : ℕ) : (n : gaussInt).im = 0 := rfl
lemma nat_cast_inj : Function.Injective (λ x : ℕ ↦ (x : gaussInt)) :=
λ x y hxy ↦ by simpa [nat_cast] using hxy

-- The Gaussian integers are nonempty.
instance : Inhabited gaussInt := ⟨⟨0, 0⟩⟩

-- The Gaussian integers have two distinct elements
instance : Nontrivial gaussInt := by
  use 0, 1
  rw [Ne, gaussInt.ext_iff]
  simp

end gaussInt

/- ! ℤ[i] IS AN EUCLIDEAN DOMAIN.

  A Euclidean domain is an integral domain `R` with a norm function `norm : R → ℕ` such that
  * 1) For every `a` and `b ≠ 0` in `R`, there exist `q` and `r` in `R` such that `a = bq + r`
       and either `r = 0` or `norm r < norm b`.
  * 2) For every `a` and `b ≠ 0` in `R`, `norm a ≤ norm (a*b)`.
-/

theorem sq_add_sq_eq_zero {α : Type*} [LinearOrderedRing α] (x y : α) :
    x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 := by
  sorry

namespace gaussInt

/-- The `norm` of `a + bi` is defined as `a^2 + b^2`. -/
def norm (x : gaussInt) := x.re^2 + x.im^2

-- Some properties of the norm function:
@[simp] theorem norm_nonneg (x : gaussInt) : 0 ≤ norm x := by
  sorry

theorem norm_eq_zero (x : gaussInt) : norm x = 0 ↔ x = 0 := by
  sorry

@[simp] lemma norm_zero : (0 : gaussInt).norm = 0 := by
  rw [norm_eq_zero]

theorem norm_pos (x : gaussInt) : 0 < norm x ↔ x ≠ 0 := by
  sorry

theorem norm_mul (x y : gaussInt) : norm (x * y) = norm x * norm y := by
  sorry

-- Coercion lemmas
@[simp] lemma coe_natAbs_norm (x : gaussInt) : (x.norm.natAbs : ℤ) = x.norm :=
Int.natAbs_of_nonneg (norm_nonneg _)

lemma nat_cast_natAbs_norm {α : Type*} [Ring α] (x : gaussInt) :
    (x.norm.natAbs : α) = x.norm := by
  rw [← Int.cast_ofNat, coe_natAbs_norm]

lemma natAbs_norm_eq (x : gaussInt) : x.norm.natAbs =
  x.re.natAbs * x.re.natAbs + x.im.natAbs * x.im.natAbs := by
  rw [← Int.coe_nat_inj']
  simp [norm]
  ring_nf
  rw [abs_eq_self]
  positivity

-- Norms of integers and natural numbers
@[simp] lemma norm_int_cast (n : ℤ) : norm n = n * n := by
  sorry

@[simp] lemma norm_nat_cast (n : ℕ) : norm n = n * n := norm_int_cast _

lemma norm_nat_cast' (n : ℕ) : (norm n).natAbs = n * n := by
  rw [norm_nat_cast]; norm_cast

/-- The `conjugate` of `a + bi` is `a - bi`. -/
def conj (x : gaussInt) : gaussInt := ⟨x.re, -x.im⟩

@[simp] theorem conj_re (x : gaussInt) : (conj x).re = x.re := rfl
@[simp] theorem conj_im (x : gaussInt) : (conj x).im = - x.im := rfl

theorem norm_conj (x : gaussInt) : norm (conj x) = norm x := by
  simp [norm]

lemma norm_eq_mul_conj (x : gaussInt) : (x.norm : gaussInt) = x * x.conj := by
  sorry

namespace Int

/-- Auxiliary definition to define quotient and remainder in ℤ[i]. -/
def div' (a b : ℤ) := (a + b / 2) / b

/-- Auxiliary definition to define quotient and remainder in ℤ[i]. -/
def mod' (a b : ℤ) := (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a := by
  rw [div', mod']
  linarith [Int.ediv_add_emod (a + b / 2) b]

theorem abs_mod'_le (a b : ℤ) (h : 0 < b): abs (mod' a b) ≤ b / 2 := by
  rw [mod', abs_le]
  constructor
  . linarith [Int.emod_nonneg (a + b / 2) h.ne']
  . have := Int.emod_lt_of_pos (a + b / 2) h
    have := Int.ediv_add_emod b 2
    have := Int.emod_lt_of_pos b zero_lt_two
    revert this; intro this -- FIXME, this should not be needed
    linarith

theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b := by linarith [div'_add_mod' a b]

end Int

/- Given Gaussian integers `x = a + bi` and `y = c + di`, their quotient as complex numbers is
 `((a + bi)*(c - di))/((c + di)*(c - di)) = (ac + bd)/(c^2 + d^2) + ((bc - ad)/(c^2 + d^2)) i`. -/

/- We define `x / y` as the Gaussian integers whose real and imaginary parts are the nearest
  integers to `(ac + bd)/(c^2 + d^2)` and `(bc - ad)/(c^2 + d^2)`. -/
instance : Div gaussInt :=
⟨λ x y ↦ ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩⟩

lemma div_def (x y : gaussInt) :
  x / y = ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩ := rfl

-- `x % y` is defined as the remainder `x % y := x - (x / y) * y`.
instance : Mod gaussInt := ⟨λ x y ↦ x - y * (x / y)⟩

lemma mod_def (x y : gaussInt) : x % y = x - y * (x / y) := rfl

-- `(x % y)` plays the role of `r` in property `1)` in the definition of Euclidean domain:
theorem norm_mod_lt (x : gaussInt) {y : gaussInt} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have norm_y_pos : 0 < norm y := by rwa [norm_pos]
  have H1 : x % y * conj y = ⟨Int.mod' (x * conj y).re (norm y), Int.mod' (x * conj y).im (norm y)⟩
  · ext <;> simp [Int.mod'_eq, mod_def, div_def, norm] <;> ring
  have H2 : norm (x % y) * norm y ≤ norm y / 2 * norm y
  · calc
      norm (x % y) * norm y = norm (x % y * conj y) := by simp only [norm_mul, norm_conj]
      _ = |Int.mod' (x.re * y.re + x.im * y.im) (norm y)| ^ 2
          + |Int.mod' (-(x.re * y.im) + x.im * y.re) (norm y)| ^ 2 := by simp [H1, norm, sq_abs]
      _ ≤ (y.norm / 2) ^ 2 + (y.norm / 2) ^ 2 := by gcongr <;> apply Int.abs_mod'_le _ _ norm_y_pos
      _ = norm y / 2 * (norm y / 2 * 2) := by ring
      _ ≤ norm y / 2 * norm y := by gcongr; apply Int.ediv_mul_le; norm_num
  calc norm (x % y) ≤ norm y / 2 := le_of_mul_le_mul_right H2 norm_y_pos
    _ < norm y := by
        apply Int.ediv_lt_of_lt_mul
        · norm_num
        · linarith

lemma natAbs_norm_mod_lt (x y : gaussInt) (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  apply Int.ofNat_lt.1
  simp only [Int.coe_natAbs, abs_of_nonneg, norm_nonneg]
  apply norm_mod_lt x hy

-- We check property `2)`:
lemma norm_le_norm_mul_left (x : gaussInt) {y : gaussInt} (hy : y ≠ 0) :
    (norm x).natAbs ≤ (norm (x * y)).natAbs := by
  sorry

-- We put everything together to get that ℤ[i] is an Euclidean domain.
instance : EuclideanDomain gaussInt :=
  { gaussInt.instCommRing with
    quotient  := (· / ·)
    remainder := (· % ·)
    quotient_mul_add_remainder_eq :=
      fun x y ↦ by simp only; rw [mod_def, add_comm, sub_add_cancel]
    quotient_zero := fun x ↦ by
      simp [div_def, norm, Int.div]
      rfl
    r               := (measure (Int.natAbs ∘ norm)).1
    r_wellFounded   := (measure (Int.natAbs ∘ norm)).2
    remainder_lt    := natAbs_norm_mod_lt
    mul_left_not_lt := λ x y hy ↦ not_lt_of_ge (norm_le_norm_mul_left x hy) }

instance : IsPrincipalIdealRing gaussInt := inferInstance
instance : UniqueFactorizationMonoid gaussInt := inferInstance
instance : IsDomain gaussInt := inferInstance

-- An element of ℤ[i]is irreducible if and only if it is prime.
example (x : gaussInt) : Irreducible x ↔ Prime x :=
PrincipalIdealRing.irreducible_iff_prime

/-! UNITS IN ℤ[i]. -/
section units

-- The units in ℤ[i] are exactly the elements of norm 1.
lemma is_unit_iff_norm_eq_one (x : gaussInt) : IsUnit x ↔ x.norm = 1 := by
  sorry

lemma isUnit_iff_norm_natAbs_eq_one (x : gaussInt):  IsUnit x  ↔ x.norm.natAbs = 1 := by
  rw [is_unit_iff_norm_eq_one]
  sorry

-- ℤ[i]* = { ±1, ± i }
lemma gaussInt_units (x : gaussInt) : IsUnit x ↔
  x ∈ ({⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩} : Set gaussInt) := by
  rw [is_unit_iff_norm_eq_one]
  constructor <;>
  intro h
  . rw [norm] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    sorry
  . rcases h with h | h | h | h <;> rw [Set.mem_singleton_iff.mp h, norm] <;> ring_nf

end units

/-! PRIMES IN ℤ[i]. -/

-- 2 ramifies in gaussInt, since `2 = -i*(1 + i)^2`, and `(1 + i)` is irreducible.
example : (2 : gaussInt) = ⟨0, -1⟩ * ⟨1, 1⟩^2 := by
  sorry

lemma irreducible_i_plus_i : Irreducible (⟨1, 1⟩ : gaussInt) := by
  by_contra hni
  rw [irreducible_iff] at hni
  push_neg at hni
  have hnu : ¬ IsUnit (⟨1, 1⟩ : gaussInt) := by
    sorry
  obtain ⟨a, b, hab, ha, hb⟩ := hni hnu
  have h2 : 2 = (norm a).natAbs * (norm b).natAbs := by
    sorry
  sorry

-- Fix a prime number `p`.
variable (p : ℕ) [hp : Fact (Nat.Prime p)]

-- Now we want to prove that `p` stays prime in `ℤ[i]` if and only if `p % 4 = 3`.

-- First, we show that if `p` is not prime in `ℤ[i]`, then we can express it as a sum
-- of squares of natural numbers.
lemma sq_add_sq_of_nat_prime_of_not_irreducible (hpi : ¬ Irreducible (p : gaussInt)) :
    ∃ a b, a^2 + b^2 = p := by
  have hpu : ¬ IsUnit (p : gaussInt) := by
    sorry
  have hab : ∃ a b, (p : gaussInt) = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    rw [irreducible_iff] at hpi
    push_neg at hpi
    exact hpi hpu
  obtain ⟨a, b, hpab, hau, hbu⟩ := hab
  have hnap : (norm a).natAbs = p := by
    have hnpab : p^2 = (norm a).natAbs * (norm b).natAbs := by
      sorry
    sorry
  sorry

-- We use our previous lemma to show that if `p % 4 = 3`, then `p` is prime in `ℤ[i]`.
lemma prime_of_nat_prime_of_mod_four_eq_three (hp3 : p % 4 = 3) : Prime (p : gaussInt) := by
  rw [← PrincipalIdealRing.irreducible_iff_prime]
  by_contra hpi
  obtain ⟨a, b, hab⟩ := sq_add_sq_of_nat_prime_of_not_irreducible p hpi
  have h4:  ∀ a b : ZMod 4, a^2 + b^2 ≠ (p : ZMod 4)
  . rw [← ZMod.nat_cast_mod p 4, hp3]
    decide
  have hab': (a : ZMod 4)^2 + (b : ZMod 4)^2 = p
  . norm_cast; apply congr_arg; exact hab
  exact h4 a b hab'

-- Now we prove the converse:
lemma mod_four_eq_three_of_nat_prime_of_prime (hpi : Prime (p : gaussInt)) :
    p % 4 = 3 := by
  -- Either `p = 2` or `p` is odd.
  cases' hp.1.eq_two_or_odd with hp2 hpo
  -- Assume `p = 2`.
  . exfalso
    rw [← PrincipalIdealRing.irreducible_iff_prime] at hpi
    sorry

   -- Assume `p` is odd and reason by contradiction:
  . by_contra hp3
    -- Since `p % 4 ≠ 3`, there exists `k : zmod p` such that `k^2 = -1`.
    obtain ⟨n, hn⟩ := (ZMod.exists_sq_eq_neg_one_iff).2 hp3
    -- We can lift this `n : zmod p` to a `k : ℕ`, `k < p`.
    obtain ⟨k, k_lt_p, rfl⟩ : ∃ (k' : ℕ) (_ : k' < p), (k' : ZMod p) = n :=
    ⟨n.val, n.val_lt, ZMod.nat_cast_zmod_val n⟩
    -- We conclude that `p ∣ k ^ 2 + 1` (in ℕ).
    have hpk : p ∣ k ^ 2 + 1
    . rw [pow_two, ← CharP.cast_eq_zero_iff (ZMod p) p, Nat.cast_add, Nat.cast_mul,
        Nat.cast_one, ← hn, add_left_neg]
    -- Hence `p ∣ (k + i)*(k - i)` (in ℤ[i]).
    have hpk' : (p : gaussInt) ∣ ({re := ↑k, im := 1} * {re := ↑k, im := -1})
    . obtain ⟨y, hy⟩ := hpk -- k^2 + 1 = p * y
      use y
      simp [mul_def]
      rw [← Nat.cast_mul, ← Nat.cast_one, ← Nat.cast_add, ← sq, hy, Nat.cast_mul]

    -- We'll need this for the next two goals
    have hkltp : 1 + k * k < p * p
    . calc 1 + k * k ≤ k + k * k := sorry
        _ = k * (k + 1) := sorry
        _ < p * p := sorry

    -- `p` does not divide `k - i`.
    have hpk₁ : ¬ (p : gaussInt) ∣ ⟨k, -1⟩
    . rintro ⟨x, hx⟩
      apply lt_irrefl (p * x : gaussInt).norm.natAbs
      calc (norm (p * x : gaussInt)).natAbs = (norm ⟨k, -1⟩).natAbs := by rw [hx]
        _ < (norm (p : gaussInt)).natAbs := by simpa [add_comm, norm, sq] using hkltp
        _ ≤ (norm (p * x : gaussInt)).natAbs := norm_le_norm_mul_left _
                (λ hx0 ↦ by simp [hx0, mul_zero, gaussInt.ext_iff] at hx)

    -- `p` does not divide `k + i`.
    have hpk₂ : ¬ (p : gaussInt) ∣ ⟨k, 1⟩
    . sorry

    -- `p` is prime in ℤ[i] and it divides `(k + i)*(k - i)`, so it divides one of the factors
    have h_dvd : (p : gaussInt) ∣ {re := ↑k, im := 1} ∨ (p : gaussInt) ∣ {re := ↑k, im := -1} :=
    hpi.2.2 ⟨k, 1⟩ ⟨k, -1⟩ hpk'

    -- We derive a contradiction from h_dvd, hpk₁ and hpk₂.
    tauto

-- Combine both directions:
theorem gaussInt_prime_iff_mod_four_eq_three_of_nat_prime : Prime (p : gaussInt) ↔ p % 4 = 3 :=
⟨mod_four_eq_three_of_nat_prime_of_prime p, prime_of_nat_prime_of_mod_four_eq_three p⟩

-- Finally, we show that if `2 < p`, then `p` is the sum of two squares if and only if
-- `p % 4 = 1`.

--Auxiliary lemma for the easy direction
lemma aux {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p) {a b : ℕ } (hab : a^2 + b^2 = p) :
    (Even a ∧ Odd b) ∨ (Odd a ∧ Even b) := by
  sorry

theorem sum_of_sq_iff_one_mod_four {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : 2 < p) :
    (∃ (a b : ℕ), a^2 + b^2 = p) ↔ p % 4 = 1 := by
  refine' ⟨λ hab ↦ _, λ hp1 ↦ _⟩
  . obtain ⟨a, b, hab⟩ := hab
    rw [← hab]
    cases' aux hp.1 hp2 hab with h h
    . obtain ⟨c, hc⟩ := (even_iff_exists_two_mul _).mp h.1
      obtain ⟨d, hd⟩ := h.2
      rw [hc, hd]
      ring_nf
      norm_num
    . sorry
  . sorry

end gaussInt

/-! More Number Theory in `mathlib` :

  * `Modular arithmetic` : Data.ZMod
  * `p-adic numbers` : NumberTheory.Padics
  * `Quadratic reciprocity` : NumberTheory.LegendreSymbol.QuadraticReciprocity
  * `Dedekind domains` : RingTheory.DedekindDomain
    * `Unique factorization of ideals` : RingTheory.DedekindDomain.Ideal
    * `Adic valuations`: RingTheory.DedekindDomain.AdicValuation
    * `Finite adeles` : RingTheory.DedekindDomain.FiniteAdeleRing
  * `Global fields` : NumberTheory.NumberField, NumberTheory.FunctionField
    * `Class numbers` : NumberTheory.ClassNumber
    * `Adeles and ideles` : coming soon!
  * `Elliptic curves` : AlgebraicGeometry.EllipticCurve
  * `Cyclotomic extensions` : NumberTheory.Cyclotomic
  * `Witt vectors` : RingTheory.WittVector
  * `L-series of arithmetic functions; Riemann zeta function` : NumberTheory.LSeries
  * `Bernouilli polynomials` : NumberTheory.NumberField.BernoulliPolynomials
  * `Liouville's theorem` : NumberTheory.Liouville
  * `Group cohomology` : RepresentationTheory.GroupCohomology
  * ...
-/
