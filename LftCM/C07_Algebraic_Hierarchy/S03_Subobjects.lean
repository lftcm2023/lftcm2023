import LftCM.C07_Algebraic_Hierarchy.S02_Morphisms
import Mathlib.GroupTheory.QuotientGroup

set_option autoImplicit true

namespace lftcm

-- .. _section_hierarchies_subobjects:
-- 
-- Sub-objects
-- -----------
-- 
-- After defining some algebraic structure and its morphisms, the next step is to consider sets
-- that inherit this algebraic structure, for instance subgroups or subrings.
-- This largely overlaps our previous topic. Indeed a set in ``X`` is implemented as a function from
-- ``X`` to ``Prop`` so sub-objects are functions satisfying a certain predicate.
-- Hence we can reuse of lot of the ideas that led to the ``FunLike`` class and its descendants.
-- We won't reuse ``FunLike`` itself because this would break the abstraction barrier from ``Set X``
-- to ``X → Prop``. Instead there is a ``SetLike`` class. Instead of wrapping an injection into a
-- function type, that class wraps an injection into a ``Set`` type and defines the corresponding
-- coercion and ``Membership`` instance.
-- 

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


-- Equipped with the above ``SetLike`` instance, we can already state naturally that
-- a submonoid ``N`` contains ``1`` without using ``N.carrier``.
-- We can also silently treat ``N`` as a set in ``M`` as take its direct image under a map.

example [Monoid M] (N : Submonoid M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid M) (α : Type) (f : M → α) := f '' N

-- We also have a coercion to ``Type`` which uses ``Subtype`` so, given a submonoid ``N`` we can write
-- a parameter ``(x : N)`` which can be coerced to an element of ``M`` belonging to ``N``.
-- 

example [Monoid M] (N : Submonoid M) (x : N) : (x : M) ∈ N := x.property

-- Using this coercion to ``Type`` we can also tackle the task of equipping a submonoid with a
-- monoid structure. We will use the coercion from the type associated to ``N`` as above, and the
-- lemma ``SetCoe.ext`` asserting this coercion is injective. Both are provided by the ``SetLike``
-- instance.
-- 

instance SubMonoidMonoid [Monoid M] (N : Submonoid M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))

-- Note that, in the above instance, instead of using the coercion to ``M`` and calling the
-- ``property`` field, we could have used destructuring binders as follows.
-- 

example [Monoid M] (N : Submonoid M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)

-- 
-- In order to apply lemmas about submonoids to subgroups or subrings, we need a class, just
-- like for morphisms. Note this class take a ``SetLike`` instance as a parameter so it does not need
-- a carrier field and can use the membership notation in its fields.

class SubmonoidClass (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass (Submonoid M) M where
  mul_mem := Submonoid.mul_mem
  one_mem := Submonoid.one_mem

-- 
-- As an exercise you should define a ``Subgroup`` structure, endow it with a ``SetLike`` instance
-- and a ``SubmonoidClass`` instance, put a ``Group`` instance on the subtype associated to a
-- ``Subgroup`` and define a ``SubgroupClass`` class.
-- 
-- Another very important thing to know about subobjects of a given algebraic object in Mathlib
-- always form a complete lattice, and this structure is used a lot. For instance you may look for
-- the lemma saying that an intersection of submonoids is a submonoid. But this won't be a lemma,
-- this will be an infimum construction. Let us do the case of two submonoids.
-- 

instance [Monoid M] : Inf (Submonoid M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

-- This allows to get the intersections of two submonoids as a submonoid.
-- 

example [Monoid M] (N P : Submonoid M) : Submonoid M := N ⊓ P

-- You may think it's a shame that we had to use the inf symbol ``⊓`` in the above example instead
-- of the intersection symbol ``∩``. But think about the supremum. The union of two submonoids is not
-- a submonoid. However submonoids still form a lattice (even a complete one). Actually ``N ⊔ P`` is
-- the submonoid generated by the union of ``N`` and ``P`` and of course it would be very confusing to
-- denote it by ``N ∪ P``. So you can see the use of ``N ⊓ P`` as much more consistent. It is also
-- a lot more consistent across various kind of algebraic structures. It may look a bit weird at first
-- to see the sum of two vector subspace ``E`` and ``F`` denoted by ``E ⊔ F`` instead of ``E + F``.
-- But you will get used to it. And soon you will consider the ``E + F`` notation as a distraction
-- emphasizing the anecdotal fact that elements of ``E ⊔ F`` can be written as a sum of an element of
-- ``E`` and an element of ``F`` instead of emphasizing the fundamental fact that ``E ⊔ F`` is the
-- smallest vector subspace containing both ``E`` and ``F``.
-- 
-- Our last topic for this chapter is that of quotients. Again we want to explain how
-- convenient notation are built and code duplication is avoided in Mathlib. Here the main device
-- is the ``HasQuotient`` class which allows notations like ``M ⧸ N``. Beware the quotient symbol
-- ``⧸`` is a special unicode character, not a regular ASCII division symbol.
-- 
-- As an example, we will build the quotient of a commutative monoid by a submonoid, leave proofs
-- to you. In the last example, you can use ``Setoid.refl`` but it won't automatically pick up
-- the relevant ``Setoid`` structure. You can fix this issue by providing all arguments using
-- the ``@`` syntax, as in ``@Setoid.refl M N.Setoid``.
-- 

def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      sorry
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

export CommSemigroup (mul_comm)

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
      sorry
        )
  mul_assoc := by
      sorry
  one := QuotientMonoid.mk N 1
  one_mul := by
      sorry
  mul_one := by
      sorry
