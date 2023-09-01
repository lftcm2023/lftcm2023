import LftCM.Common
import LftCM.C07_Algebraic_Hierarchy.S02_Morphisms
import Mathlib.GroupTheory.QuotientGroup

set_option autoImplicit true

namespace lftcm


@[ext]
structure Submonoid (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid M) M where
  coe := Submonoid.carrier
  coe_injective' := Submonoid.ext



example [Monoid M] (N : Submonoid M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid M) (α : Type) (f : M → α) := f '' N


example [Monoid M] (N : Submonoid M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoidMonoid [Monoid M] (N : Submonoid M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass (Submonoid M) M where
  mul_mem := Submonoid.mul_mem
  one_mem := Submonoid.one_mem

@[ext]
structure Subgroup (G : Type) [Group G] extends Submonoid G where
  /-- The inverse of an element of a subgroup belongs to the subgroup. -/
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier


/-- Subgroups in `M` can be seen as sets in `M`. -/
instance [Group G] : SetLike (Subgroup G) G where
  coe := fun H ↦ H.toSubmonoid.carrier
  coe_injective' := Subgroup.ext

instance [Group G] (H : Subgroup G) : Group H :=
{ SubMonoidMonoid H.toSubmonoid with
  inv := fun x ↦ ⟨x⁻¹, H.inv_mem x.property⟩
  mul_left_inv := fun x ↦ SetCoe.ext (Group.mul_left_inv (x : G))
  }

class SubgroupClass (S : Type) (G : Type) [Group G] [SetLike S G]
    extends SubmonoidClass S G  : Prop where
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance [Group G] : SubmonoidClass (Subgroup G) G where
  mul_mem := fun H ↦ H.toSubmonoid.mul_mem
  one_mem := fun H ↦ H.toSubmonoid.one_mem

instance [Group G] : SubgroupClass (Subgroup G) G :=
{ (inferInstance : SubmonoidClass (Subgroup G) G) with
  inv_mem := Subgroup.inv_mem }


instance [Monoid M] : Inf (Submonoid M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid M) : Submonoid M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      rintro a b c ⟨w, hw, z, hz, h⟩ ⟨w', hw', z', hz', h'⟩
      refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩
      rw [← mul_assoc, h, CommSemigroup.mul_comm b, mul_assoc, h', ← mul_assoc, CommSemigroup.mul_comm z, mul_assoc]
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

export CommSemigroup (mul_comm)

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
    rintro a₁ b₁ ⟨w, hw, z, hz, ha⟩ a₂ b₂ ⟨w', hw', z', hz', hb⟩
    refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩
    rw [mul_comm w, ← mul_assoc, mul_assoc a₁, hb, mul_comm, ← mul_assoc, mul_comm w, ha,
        mul_assoc, mul_comm z, mul_assoc b₂, mul_comm z', mul_assoc]
        )
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    apply Quotient.sound
    dsimp only
    rw [mul_assoc]
    apply @Setoid.refl M N.Setoid
  one := QuotientMonoid.mk N 1
  one_mul := by
    rintro ⟨a⟩ ; apply Quotient.sound ; dsimp only ; rw [one_mul] ; apply @Setoid.refl M N.Setoid
  mul_one := by
    rintro ⟨a⟩ ; apply Quotient.sound ; dsimp only ; rw [mul_one] ; apply @Setoid.refl M N.Setoid

end lftcm
