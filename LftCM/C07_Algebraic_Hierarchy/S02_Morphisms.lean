import LftCM.Common
import LftCM.C07_Algebraic_Hierarchy.S01_Basics
import Mathlib.Topology.Instances.Real

set_option autoImplicit true

namespace lftcm


def isMonoidHom_naive [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'
structure isMonoidHom [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'
example : Continuous (id : ℝ → ℝ) := continuous_id
@[ext]
structure MonoidHom (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'

instance [Monoid G] [Monoid H] : CoeFun (MonoidHom G H) (fun _ ↦ G → H) where
  coe := MonoidHom.toFun

attribute [coe] MonoidHom.toFun


example [Monoid G] [Monoid H] (f : MonoidHom G H) : f 1 = 1 :=  f.map_one

@[ext]
structure AddMonoidHom (G H : Type) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom.toFun

attribute [coe] AddMonoidHom.toFun

@[ext]
structure RingHom (R S : Type) [Ring R] [Ring S] extends MonoidHom R S, AddMonoidHom R S



class MonoidHomClass_bad (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'


def badInst [Monoid M] [Monoid N] [MonoidHomClass_bad F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass_bad.toFun


class MonoidHomClass' (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance [Monoid M] [Monoid N] [MonoidHomClass' F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass'.toFun

attribute [coe] MonoidHomClass'.toFun


instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass' (MonoidHom M N) M N where
  toFun := MonoidHom.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass' (RingHom R S) R S where
  toFun := fun f ↦ f.toMonoidHom.toFun
  map_one := fun f ↦ f.toMonoidHom.map_one
  map_mul := fun f ↦ f.toMonoidHom.map_mul


lemma map_inv_of_inv [Monoid M] [Monoid N] [MonoidHomClass' F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass'.map_mul, h, MonoidHomClass'.map_one]

example [Monoid M] [Monoid N] (f : MonoidHom M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map_inv_of_inv f h

example [Ring R] [Ring S] (f : RingHom R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map_inv_of_inv f h



class MonoidHomClass (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    FunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass (MonoidHom M N) M N where
  coe := MonoidHom.toFun
  coe_injective' := MonoidHom.ext
  map_one := MonoidHom.map_one
  map_mul := MonoidHom.map_mul


@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', LE.le a a' → toFun a ≤ toFun a'

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
MonoidHom M N, OrderPresHom M N

class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β]

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    MonoidHomClass (OrderPresMonoidHom α β) α β
  := sorry
