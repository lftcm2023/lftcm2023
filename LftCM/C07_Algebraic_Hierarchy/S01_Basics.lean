import LftCM.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit true

namespace lftcm


class One (α : Type) where
  /-- The element one -/
  one : α


#check One.one -- lftcm.One.one {α : Type} [self : One₁ α] : α

@[class] structure One' (α : Type) where
  /-- The element one -/
  one : α

#check One'.one -- lftcm.One'.one {α : Type} (self : One' α) : α


example (α : Type) [One α] : α := One.one

example (α : Type) [One α] := (One.one : α)

@[inherit_doc]
notation "𝟙" => One.one

example {α : Type} [One α] : α := 𝟙

example {α : Type} [One α] : (𝟙 : α) = 𝟙 := rfl


class Dia (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia.dia


class SemigroupDia (α : Type) where
  toDia : Dia α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)


attribute [instance] SemigroupDia.toDia

example {α : Type} [SemigroupDia α] (a b : α) : α := a ⋄ b


class SemigroupDia' (α : Type) extends Dia α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [SemigroupDia' α] (a b : α) : α := a ⋄ b

class DiaOneClass (α : Type) extends One α, Dia α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a



set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass α] (a b : α) : Prop := a ⋄ b = 𝟙


class MonoidDia (α : Type) extends SemigroupDia α, DiaOneClass α


class MonoidDiaBad (α : Type) where
  toSemigroupDia : Semigroup α
  toDiaOneClass : DiaOneClass α


example {α : Type} [MonoidDia α] :
  (MonoidDia.toSemigroupDia.toDia.dia : α → α → α) = MonoidDia.toDiaOneClass.toDia.dia := rfl


/- lftcm.MonoidDiaBad.mk {α : Type} (toSemigroupDia : Semigroup α) (toDiaOneClass : DiaOneClass α) : MonoidDiaBad α -/
#check MonoidDiaBad.mk

/- lftcm.MonoidDia.mk {α : Type} [toSemigroupDia : SemigroupDia α] [toOne : One α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a)
  (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : MonoidDia α
-/
#check MonoidDia.mk


#check MonoidDia.toSemigroupDia
#check MonoidDia.toDiaOneClass



class Inv (α : Type) where
  /-- The inversion function -/
  inv : α → α


@[inherit_doc]
postfix:max "⁻¹" => Inv.inv

class GroupDia (G : Type) extends MonoidDia G, Inv G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙


lemma left_inv_eq_right_inv {M : Type} [MonoidDia M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass.one_dia c, ← hba, SemigroupDia.dia_assoc, hac, DiaOneClass.dia_one b]


export DiaOneClass (one_dia dia_one)
export SemigroupDia (dia_assoc)
export GroupDia (inv_dia)


example {M : Type} [MonoidDia M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]


lemma inv_eq_of_dia [GroupDia G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b :=
  sorry

lemma dia_inv [GroupDia G] (a : G) : a ⋄ a⁻¹ = 𝟙 :=
  sorry



class AddSemigroup (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive]
class Semigroup (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid (α : Type) extends AddSemigroup α, AddZeroClass α

@[to_additive]
class Monoid (α : Type) extends Semigroup α, MulOneClass α

attribute [to_additive existing] Monoid.toMulOneClass

export Semigroup (mul_assoc)
export AddSemigroup (add_assoc)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc, hac, mul_one b]

#check left_neg_eq_right_neg'

class Neg (α : Type) where
  /-- The negation function -/
  neg : α → α

@[inherit_doc]
prefix:max "-" => Neg.neg

class AddCommSemigroup (α : Type) extends AddSemigroup α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive]
class CommSemigroup (α : Type) extends Semigroup α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid (α : Type) extends AddMonoid α, AddCommSemigroup α

@[to_additive]
class CommMonoid (α : Type) extends Monoid α, CommSemigroup α

class AddGroup (G : Type) extends AddMonoid G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive]
class Group (G : Type) extends Monoid G, Inv G where
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1


attribute [simp] Group.mul_left_inv AddGroup.neg_add




attribute [to_additive] Inv

@[to_additive]
lemma inv_eq_of_mul {G : Type} [Group G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
  sorry


@[to_additive (attr := simp)]
lemma Group.mul_inv {G : Type} [Group G] {a : G} : a * a⁻¹ = 1 := by
  sorry

@[to_additive]
lemma mul_left_cancel {G : Type} [Group G] {a b c : G} (h : a * b = a * c) : b = c := by
  sorry

@[to_additive]
lemma mul_right_cancel {G : Type} [Group G] {a b c : G} (h : b*a = c*a) : b = c := by
  sorry

class AddCommGroup (G : Type) extends AddGroup G, AddCommMonoid G

@[to_additive]
class CommGroup (G : Type) extends Group G, CommMonoid G



class Ring (R : Type) extends AddGroup R, Monoid R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring R] : AddCommGroup R :=
{ Ring.toAddGroup with
  add_comm := by
    sorry }

instance : Ring ℤ where
  add := (· + ·)
  add_assoc := _root_.add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (-(·))
  neg_add := by simp
  mul := (· * ·)
  mul_assoc := _root_.mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

class LE (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤ " => LE.le

class Preorder (α : Type)

class PartialOrder (α : Type)

class OrderedCommMonoid (α : Type)

instance : OrderedCommMonoid ℕ where

class SMul (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul.smul


class Module (R : Type) [Ring R] (M : Type) [AddCommGroup M] extends SMul R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

instance selfModule (R : Type) [Ring R] : Module R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc
  add_smul := Ring.right_distrib
  smul_add := Ring.left_distrib

def nsmul [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul n a

def zsmul {M : Type} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul n a
  | Int.negSucc n, a => -(nsmul n.succ a)
instance abGrpModule (A : Type) [AddCommGroup A] : Module ℤ A where
  smul := zsmul
  zero_smul := by simp [zsmul, nsmul]
  one_smul := by simp [zsmul, nsmul]
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry

#synth Module ℤ ℤ -- abGrpModule ℤ


class AddMonoid' (M : Type) extends AddSemigroup M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid' M] : SMul ℕ M := ⟨AddMonoid'.nsmul⟩

instance (M N : Type) [AddMonoid' M] [AddMonoid' N] : AddMonoid' (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc := fun a b c ↦ by ext <;> apply add_assoc
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero

instance : AddMonoid' ℤ where
  add := (· + ·)
  add_assoc := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
