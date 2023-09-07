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
  constructor <;>
  intro h
  . by_contra' hne
    by_cases hx : x = 0
    . rw [hx, zero_pow zero_lt_two, zero_add] at h
      exact pow_ne_zero 2 (hne hx ) h
    . have hx2 : 0 < x^2 := pow_two_pos_of_ne_zero x hx
      have hy2 : 0 ≤ y^2 := pow_two_nonneg y
      have hxy : 0 < x^2 + y^2 := add_pos_of_pos_of_nonneg hx2 hy2
      exact (ne_of_gt hxy) h
  . rw [h.1, h.2, zero_pow zero_lt_two, zero_add]

namespace gaussInt

/-- The `norm` of `a + bi` is defined as `a^2 + b^2`. -/
def norm (x : gaussInt) := x.re^2 + x.im^2

-- Some properties of the norm function:
@[simp] theorem norm_nonneg (x : gaussInt) : 0 ≤ norm x :=
add_nonneg (pow_two_nonneg _) (pow_two_nonneg _)

theorem norm_eq_zero (x : gaussInt) : norm x = 0 ↔ x = 0 := by
  rw [norm, sq_add_sq_eq_zero, gaussInt.ext_iff]; rfl

@[simp] lemma norm_zero : (0 : gaussInt).norm = 0 := by
  rw [norm_eq_zero]

theorem norm_pos (x : gaussInt) : 0 < norm x ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, ne_comm, Ne.def, norm_eq_zero]
  simp only [norm_nonneg, true_and]

theorem norm_mul (x y : gaussInt) : norm (x * y) = norm x * norm y := by
  simp only [norm, mul_re, mul_im]; ring_nf

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
  simp [norm, sq]

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
  simp [norm, mul_def, sq]; ring_nf; rfl

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
  rw [norm_mul, Int.natAbs_mul]
  apply le_mul_of_one_le_right (Nat.zero_le _)
  apply Int.ofNat_le.1
  rw [coe_natAbs_norm]
  exact Int.add_one_le_of_lt ((norm_pos _).mpr hy)

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
  constructor <;>
  intro h
  . obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp h
    have hxy : (x * y).norm = 1
    . rw [hy, norm]
      ring_nf
    rw [norm_mul] at hxy
    exact Int.eq_one_of_mul_eq_one_right (norm_nonneg _) hxy
  . rw [isUnit_iff_exists_inv]
    use x.conj
    rw [← norm_eq_mul_conj, h]
    rfl

lemma isUnit_iff_norm_natAbs_eq_one (x : gaussInt):  IsUnit x  ↔ x.norm.natAbs = 1 := by
  rw [is_unit_iff_norm_eq_one, Int.natAbs_eq_iff]
  refine' ⟨λ h ↦ Or.inl h, λ h ↦ _⟩
  have hx : ¬ x.norm = -↑1
  . intro hx
    linarith [norm_nonneg x]
  exact (or_iff_left hx).mp h

-- ℤ[i]* = { ±1, ± i }
lemma gaussInt_units (x : gaussInt) : IsUnit x ↔
  x ∈ ({⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩} : Set gaussInt) := by
  rw [is_unit_iff_norm_eq_one]
  constructor <;>
  intro h
  . rw [norm] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hre : x.re = 0
    . simp [hre] at h
      cases' h with hp hn
      . right; right; left; rw [mk_def x, hre, hp]
      . right; right; right; rw [mk_def x, hre, hn]
    . have him : x.im = 0 := by
        by_contra hne
        have : (2 : ℤ) ≤ 1 :=
        calc 2 = 1 + 1 := by rfl
           _ ≤ x.re^2 + x.im^2 := by
              exact add_le_add (Int.cast_one_le_of_pos (pow_two_pos_of_ne_zero _ hre))
                (Int.cast_one_le_of_pos (pow_two_pos_of_ne_zero _ hne))
           _ = 1 := h
        linarith
      simp [him] at h
      cases' h with hp hn
      . left; rw [mk_def x, him, hp]
      . right; left; rw [mk_def x, him, hn]
  . rcases h with h | h | h | h <;> rw [Set.mem_singleton_iff.mp h, norm] <;> ring_nf

end units

/-! PRIMES IN ℤ[i]. -/

-- 2 ramifies in gaussInt, since `2 = -i*(1 + i)^2`, and `(1 + i)` is irreducible.
example : (2 : gaussInt) = ⟨0, -1⟩ * ⟨1, 1⟩^2 := by
  simp [pow_two, mul_def]; rfl

lemma irreducible_i_plus_i : Irreducible (⟨1, 1⟩ : gaussInt) := by
  by_contra hni
  rw [irreducible_iff] at hni
  push_neg at hni
  have hnu : ¬ IsUnit (⟨1, 1⟩ : gaussInt) := by
    simp [is_unit_iff_norm_eq_one, norm]
  obtain ⟨a, b, hab, ha, hb⟩ := hni hnu
  have h2 : 2 = (norm a).natAbs * (norm b).natAbs := by
    rw [← Int.natAbs_mul, ← norm_mul, ← hab, norm]
    simp
  suffices h : (norm a).natAbs = 1 ∨ (norm b).natAbs = 1 by
    rw [isUnit_iff_norm_natAbs_eq_one] at ha hb
    cases' h with ha1 hb1
    exacts [ha ha1, hb hb1]
  rw [← Nat.isUnit_iff, ← Nat.isUnit_iff]
  apply of_irreducible_mul
  rw [← h2, Nat.irreducible_iff_nat_prime]
  exact Nat.prime_two

-- Fix a prime number `p`.
variable (p : ℕ) [hp : Fact (Nat.Prime p)]

-- Now we want to prove that `p` stays prime in `ℤ[i]` if and only if `p % 4 = 3`.

-- First, we show that if `p` is not prime in `ℤ[i]`, then we can express it as a sum
-- of squares of natural numbers.
lemma sq_add_sq_of_nat_prime_of_not_irreducible (hpi : ¬ Irreducible (p : gaussInt)) :
    ∃ a b, a^2 + b^2 = p := by
  have hpu : ¬ IsUnit (p : gaussInt) := by
    rw [is_unit_iff_norm_eq_one, norm_nat_cast, ← Nat.cast_mul, Nat.cast_eq_one, mul_eq_one,
      and_self]
    exact λ h ↦ (ne_of_lt hp.1.one_lt).symm h
  have hab : ∃ a b, (p : gaussInt) = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    rw [irreducible_iff] at hpi
    push_neg at hpi
    exact hpi hpu
  obtain ⟨a, b, hpab, hau, hbu⟩ := hab
  have hnap : (norm a).natAbs = p := by
    have hnpab : p^2 = (norm a).natAbs * (norm b).natAbs := by
      rw [sq, ← norm_nat_cast', hpab, norm_mul, Int.natAbs_mul]
    rw [isUnit_iff_norm_natAbs_eq_one] at hau hbu
    rw [eq_comm, Nat.Prime.mul_eq_prime_sq_iff hp.1 hau hbu] at hnpab
    exact hnpab.1
  use a.re.natAbs
  use a.im.natAbs
  rw [sq, sq, ← natAbs_norm_eq]
  exact hnap

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
    have h2 : ¬ Irreducible (2 : gaussInt)
    . rw [irreducible_iff]
      push_neg
      rintro -
      exact ⟨⟨1, 1⟩, ⟨1, -1⟩, by simp [mul_def]; rfl, by simp [is_unit_iff_norm_eq_one, norm]⟩
    rw [hp2] at hpi
    exact h2 hpi

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
    . calc 1 + k * k ≤ k + k * k := add_le_add_right (Nat.one_le_iff_ne_zero.mpr
              (λ hk0 ↦ by clear_aux_decl; simp [*, pow_succ'] at *)) _
        _ = k * (k + 1) := by simp [add_comm, mul_add]
        _ < p * p := mul_lt_mul k_lt_p k_lt_p (Nat.succ_pos _) (Nat.zero_le _)

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
    . rintro ⟨x, hx⟩
      apply lt_irrefl (p * x : gaussInt).norm.natAbs
      calc (norm (p * x : gaussInt)).natAbs = (norm ⟨k, 1⟩).natAbs := by rw [hx]
        _ < (norm (p : gaussInt)).natAbs := by simpa [add_comm, norm, sq] using hkltp
        _ ≤ (norm (p * x : gaussInt)).natAbs := norm_le_norm_mul_left _
                (λ hx0 ↦ by simp [hx0, mul_zero, gaussInt.ext_iff] at hx)

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
  by_contra' h
  rw [← Nat.even_iff_not_odd, Nat.odd_iff_not_even] at h
  have hp_even : p = 2
  . rw [← hp.even_iff, ← hab, Nat.even_add, Nat.even_pow' two_ne_zero, Nat.even_pow' two_ne_zero]
    tauto
  linarith

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
    . obtain ⟨c, hc⟩ := (even_iff_exists_two_mul _).mp h.2
      obtain ⟨d, hd⟩ := h.1
      rw [hc, hd]
      ring_nf
      norm_num
  . apply sq_add_sq_of_nat_prime_of_not_irreducible
    rw [PrincipalIdealRing.irreducible_iff_prime,
      gaussInt_prime_iff_mod_four_eq_three_of_nat_prime]
    intro hp3
    rw [hp3] at hp1
    simp only [Nat.bit1_eq_one, Nat.one_ne_zero] at hp1

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
