import LftCM.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit true

namespace lftcm

-- .. _section_hierarchies_basics:
-- 
-- Basics
-- ------
-- 
-- At the very bottom of all hierarchies in Lean, we find data-carrying
-- classes. The following class records that the given type ``α`` is endowed with
-- a distinguished element called ``one``. At this stage, it has no property at all.

class One (α : Type) where
  /-- The element one -/
  one : α

-- Since we'll make a much heavier use of classes in this chapter, we need to understand some
-- more details about what the ``class`` command is doing.
-- First, the ``class`` command above defines a structure ``One`` with parameter ``α : Type`` and
-- a single field ``one``. It also marks this structure as a class so that arguments of type
-- ``One α`` for some type ``α`` will be inferrable using the instance resolution procedure,
-- as long as they are marked as instance-implicit, ie appear between square brackets.
-- Those two effects could also have been achieved using the ``structure`` command with ``class``
-- attribute, ie writing ``@[class] structure`` instance of ``class``. But the class command also
-- ensures that ``One α`` appears as an instance-implicit argument in its own fields. Compare:

#check One.one -- lftcm.One.one {α : Type} [self : One₁ α] : α

@[class] structure One' (α : Type) where
  /-- The element one -/
  one : α

#check One'.one -- lftcm.One'.one {α : Type} (self : One' α) : α

-- In the second check, we can see that ``self : One' α`` is an explicit argument.
-- Let us make sure the first version is indeed usable without any explicit argument.

example (α : Type) [One α] : α := One.one

-- Remark: in the above example, the argument ``One α`` is marked as instance-implicit,
-- which is a bit silly since this affects only *uses* of the declaration and declaration created by
-- the ``example`` command cannot be used. However it allows to avoid giving a name to that
-- argument and, more importantly, it starts installing the good habit of marking ``One α``
-- arguments as instance-implicit.
-- 
-- Another remark is that all this will work only when Lean knows what is ``α``. In the above
-- example, leaving out the type ascription ``: α`` would generate an error message like:
-- ``typeclass instance problem is stuck, it is often due to metavariables One (?m.263 α)``
-- where ``?m.263 α`` means "some type depending on ``α``" (and 263 is simply an auto-generated
-- index that would be useful to distinguish between several unknown things). Another way
-- to avoid this issue would be to use a type annotation, as in:
example (α : Type) [One α] := (One.one : α)

-- You may have already encountered that issue when playing with limits of sequences
-- in :numref:`sequences_and_convergence` if you tried to state for instance that
-- ``0 < 1`` without telling Lean whether you meant this inequality to be about natural numbers
-- or real numbers.
-- 
-- Our next task is to assign a notation to ``One.one``. Since we don't want collisions
-- with the builtin notation for ``1``, we will use ``𝟙``. This is achieved by the following
-- command where the first line tells Lean to use the documentation
-- of ``One.one`` as documentation for the symbol ``𝟙``.
@[inherit_doc]
notation "𝟙" => One.one

example {α : Type} [One α] : α := 𝟙

example {α : Type} [One α] : (𝟙 : α) = 𝟙 := rfl

-- We now want a data-carrying class recording a binary operation. We don't want to choose
-- between addition and multiplication for now so we'll use diamond.

class Dia (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia.dia

-- As in the ``One`` example, the operation has no property at all at this stage. Let us
-- now define the class of semigroup structures where the operation is denoted by ``⋄``.
-- For now, we define it by hand as a structure with two fields, a ``Dia`` instance and some
-- ``Prop``-valued field ``dia_assoc`` asserting associativity of ``⋄``.

class SemigroupDia (α : Type) where
  toDia : Dia α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

-- Note that while stating `dia_assoc`, the previously defined field `toDia` is in the local
-- context hence can be used when Lean searches for an instance of `Dia α` to make sense
-- of `a ⋄ b`. However this `toDia` field does not become part of the type class instances database.
-- Hence doing ``example {α : Type} [SemigroupDia α] (a b : α) : α := a ⋄ b`` would fail with
-- error message ``failed to synthesize instance Dia α``.
-- 
-- We can fix this by adding the ``instance`` attribute later.

attribute [instance] SemigroupDia.toDia

example {α : Type} [SemigroupDia α] (a b : α) : α := a ⋄ b

-- Before building up, we need a more convenient way to extend structures than explicitly
-- writing fields like `toDia` and adding the instance attribute by hand. The ``class``
-- supports this using the ``extends`` syntax as in:

class SemigroupDia' (α : Type) extends Dia α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [SemigroupDia' α] (a b : α) : α := a ⋄ b

-- Note this syntax is also available in the ``structure`` command, although it that
-- case it fixes only the hurdle of writing fields such as `toDia` since there
-- is no instance to define in that case.
-- 
-- 
-- Let us now try to combine a diamond operation and a distinguished one with axioms saying
-- this element is neutral on both sides.
class DiaOneClass (α : Type) extends One α, Dia α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a


-- In the next example, we tell Lean that ``α`` has a ``DiaOneClass`` structure and state a
-- property that uses both a `Dia` instance and a `One` instance. In order to see how Lean finds
-- those instances we set a tracing option whose result can be seen in the info view. This result
-- is rather terse by default but can be expended by clicking one lines ending with black arrows.
-- It includes failed attempts where Lean tried to find instances before having enough type
-- information to succeed. The successful attempts do involve the instances generated by the
-- ``extends`` syntax.

set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass α] (a b : α) : Prop := a ⋄ b = 𝟙

-- Note that we don't need to include extra fields where combining existing classes. Hence we can
-- define monoids as:

class MonoidDia (α : Type) extends SemigroupDia α, DiaOneClass α

-- While the above definition seems straightforward, it hides an important subtlety. Both
-- ``SemigroupDia α`` and ``DiaOneClass α`` extend ``Dia α``, so one could fear that having
-- a ``Monoid α`` instance gives two unrelated diamond operations on ``α``, one coming from
-- a field ``MonoidDia.toSemigroupDia`` and one coming from a field ``MonoidDia.toDiaOneClass``.
-- 
-- Indeed if we try to build a monoid class by hand using:

class MonoidDiaBad (α : Type) where
  toSemigroupDia : Semigroup α
  toDiaOneClass : DiaOneClass α

-- then we get two completely unrelated diamond operations
-- ``MonoidDiaBad.toSemigroupDia.toDia.dia`` and ``MonoidDiaBad.toDiaOneClass.toDia.dia``.
-- 
-- The version generated using the ``extends`` syntax does not have this defect.

example {α : Type} [MonoidDia α] :
  (MonoidDia.toSemigroupDia.toDia.dia : α → α → α) = MonoidDia.toDiaOneClass.toDia.dia := rfl

-- So the ``class`` command did some magic for us (and the ``structure`` command would have done it
-- too). An easy way to see what are the fields of our classes is to check their constructor. Compare:

/- lftcm.MonoidDiaBad.mk {α : Type} (toSemigroupDia : Semigroup α) (toDiaOneClass : DiaOneClass α) : MonoidDiaBad α -/
#check MonoidDiaBad.mk

/- lftcm.MonoidDia.mk {α : Type} [toSemigroupDia : SemigroupDia α] [toOne : One α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a)
  (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : MonoidDia α
-/
#check MonoidDia.mk

-- So we see that ``Monoid`` takes ``Semigroup α`` argument as expected but then it won't
-- take a would-be overlapping ``DiaOneClass α`` argument but instead tears it apart and includes
-- only the non-overlapping parts. And it also auto-generated an instance ``Monoid.toDiaOneClass``
-- which is *not* a field but has the expected signature which, from the end-user point of view,
-- restores the symmetry between the two extended classes ``Semigroup`` and ``DiaOneClass``.

#check MonoidDia.toSemigroupDia
#check MonoidDia.toDiaOneClass

-- We are now very close to defining groups. We could add to the monoid structure a field asserting
-- the existence of an inverse for every element. But then we would need to work to access these
-- inverses. In practice it is more convenient to add it as data. To optimize reusability,
-- we define a new data-carrying class, and then give it some notation.


class Inv (α : Type) where
  /-- The inversion function -/
  inv : α → α


@[inherit_doc]
postfix:max "⁻¹" => Inv.inv

class GroupDia (G : Type) extends MonoidDia G, Inv G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙

-- The above definition may seem too weak, we only ask that ``a⁻¹`` is a left-inverse of ``a``.
-- But the other side is automatic. In order to prove that, we need a preliminary lemma.

lemma left_inv_eq_right_inv {M : Type} [MonoidDia M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass.one_dia c, ← hba, SemigroupDia.dia_assoc, hac, DiaOneClass.dia_one b]

-- In this lemma, it is pretty annoying to give full names, especially since it requires knowing
-- which part of the hierarchy provides those facts. One way to fix this is to use the ``export``
-- command to copy those facts as lemmas in the root name space.

export DiaOneClass (one_dia dia_one)
export SemigroupDia (dia_assoc)
export GroupDia (inv_dia)

-- We can then rewrite the above proof as:

example {M : Type} [MonoidDia M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]

-- It is now your turn to prove things about our algebraic structures.

lemma inv_eq_of_dia [GroupDia G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b :=
  sorry

lemma dia_inv [GroupDia G] (a : G) : a ⋄ a⁻¹ = 𝟙 :=
  sorry
-- At this stage we would like to move on to define rings, but there is a serious issue.
-- A ring structure on a type contains both an additive group structure and a multiplicative
-- monoid structure, and some properties about their interaction. But so far we hard-coded
-- a notation ``⋄`` for all our operations. More fundamentally, the type class system
-- assumes every type has only one instance of each type class. There are various
-- ways to solve this issue. Surprisingly Mathlib uses the naive idea to duplicate
-- everything for additive and multiplicative theories with the help of some code-generating
-- attribute. Structures and classes are defined in both additive and multiplicative notation
-- with an attribute ``to_additive`` linking them. In case of multiple inheritance like for
-- semi-groups, the auto-generated "symmetry-restoring" instances need also to be marked.
-- This is a bit technical you don't need to understand details. The important point is that
-- lemmas are then only stated in multiplicative notation and marked with the attribute ``to_additive``
-- to generate the additive version as ``left_inv_eq_right_inv'`` with it's auto-generated additive
-- version ``left_neg_eq_right_neg'``. In order to check the name of this additive version we
-- used the ``whatsnew in`` command on top of ``left_inv_eq_right_inv'``.



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

-- Equipped with this technology, we can easily define also commutative semigroups, monoids and
-- groups, and then define rings.
-- 
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

-- We should remember to tagged lemmas with ``simp`` when appropriate.

attribute [simp] Group.mul_left_inv AddGroup.neg_add


-- Then we need to repeat ourselves a bit since we switch to standard notations, but at least
-- ``to_additive`` does the work of translating from the multiplicative notation to the additive one.


attribute [to_additive] Inv

@[to_additive]
lemma inv_eq_of_mul {G : Type} [Group G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
  sorry

-- Note that ``to_additive`` can be ask to tag a lemma with ``simp`` and propagate that attribute
-- to the additive version as follows.

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


-- We are now ready for rings. For demonstration purposes we won't assume that addition is
-- commutative, and then immediately provide an instance of ``AddCommGroup``. Mathlib does not
-- play this game, first because in practice this does not make any ring instance easier and
-- also because Mathlib's algebraic hierarchy goes through semi-rings which are like rings but without
-- opposites so that the proof below does not work for them. What we gain here, besides a nice exercise
-- if you have never seen it, is an example of building an instance using the syntax that allows
-- to provide a parent structure and some extra fields.

class Ring (R : Type) extends AddGroup R, Monoid R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring R] : AddCommGroup R :=
{ Ring.toAddGroup with
  add_comm := by
    sorry }
-- Of course we can also build concrete instances, such as a ring structure on integers (of course
-- the instance below uses that all the work is already done in Mathlib).

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
-- As an exercise you can now set up a simple hierarchy for order relations, including a class
-- for ordered commutative monoids, which have both a partial order and a commutative monoid structure
-- such that ``∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b``. Of course you need to add fields and maybe
-- ``extends`` clauses to the following classes.

class LE (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤ " => LE.le

class Preorder (α : Type) -- fill it in

class PartialOrder (α : Type) -- fill it in

class OrderedCommMonoid (α : Type) -- fill it in

instance : OrderedCommMonoid ℕ where -- fill it in
-- 
-- 
-- 
-- We now want to discuss algebraic structures involving several types. The prime example
-- is modules over rings. If you don't know what is a module, you can pretend it means vector space
-- and think that all our rings are fields. Those structures are commutative additive groups
-- equipped with a scalar multiplication by elements of some ring.
-- 
-- We first define the data-carrying type class of scalar multiplication by some type ``α`` on some
-- type ``β``, and give it a right associative notation.

class SMul (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul.smul

-- Then we can define modules (again think about vector spaces if you don't know what is a module).

class Module (R : Type) [Ring R] (M : Type) [AddCommGroup M] extends SMul R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

-- There is something interesting going on here. While it isn't too surprising that the
-- ring structure on ``R`` is a parameter in this definition, you probably expected ``AddCommGroup M``
-- to be part of the ``extends`` clause just as ``SMul R M`` is.  Trying to do that would lead
-- to a mysterious sounding error message:
-- ``cannot find synthesization order for instance Module₁.toAddCommGroup₃ with type (R : Type) → [inst : Ring R] → {M : Type} → [self : Module R M] → AddCommGroup M
-- all remaining arguments have metavariables: Ring ?R @Module ?R ?inst✝ M``.
-- In order to understand this message, you need to remember that such an ``extends`` clause would
-- lead to a field ``Module.toAddCommGroup`` marked as an instance. This instance
-- would have the signature appearing in the error message:
-- ``(R : Type) → [inst : Ring R] → {M : Type} → [self : Module R M] → AddCommGroup M``.
-- With such an instance in the type class database, each time Lean would look for a
-- ``AddCommGroup M`` instance for some ``M``, it would need to go hunting for a completely
-- unspecified type ``R`` and a ``Ring R`` instance before embarking on the main quest of finding a
-- ``Module R M`` instance. Those two side-quests are represented by the meta-variables mentioned in
-- the error message and denoted by ``?R`` and ``?inst✝`` there. Such a ``Module.toAddCommGroup``
-- instance would then be a huge trap for the instance resolution procedure and then ``class`` command
-- refuses to set it up.
-- 
-- What about ``extends SMul R M`` then? That one creates a field
-- ``Module.toSMul : {R : Type} →  [inst : Ring R] → {M : Type} → [inst_1 : AddCommGroup M] → [self : Module R M] → SMul R M``
-- whose end result ``SMul R M`` mentions both ``R`` and ``M`` so this field can
-- safely be used as an instance. The rule is easy to remember: each class appearing in the
-- ``extends`` clause should mention every type appearing in the parameters.
-- 
-- Let us create our first module instance: a ring is a module over itself using its multiplication
-- as a scalar multiplication.
instance selfModule (R : Type) [Ring R] : Module R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc
  add_smul := Ring.right_distrib
  smul_add := Ring.left_distrib
-- As a second example, every abelian group is a module over ``ℤ`` (this is one of the reason to
-- generalize the theory of vector spaces by allowing non-invertible scalars). First one can define
-- scalar multiplication by a natural number for any type equipped with a zero and an addition:
-- ``n • a`` is defined as ``a + ⋯ + a`` where ``a`` appears ``n`` times. Then this is extended
-- to scalar multiplication by an integer by ensuring ``(-1) • a = -a``.

def nsmul [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul n a

def zsmul {M : Type} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul n a
  | Int.negSucc n, a => -(nsmul n.succ a)
-- Proving this gives rise to a module structure is a bit tedious and not interesting for the
-- current discussion, so we will sorry all axioms. You are *not* asked to replace those sorries
-- with proofs. If you insist on doing it then you will probably want to state and prove several
-- intermediate lemmas about ``nsmul`` and ``zsmul``.
instance abGrpModule (A : Type) [AddCommGroup A] : Module ℤ A where
  smul := zsmul
  zero_smul := by simp [zsmul, nsmul]
  one_smul := by simp [zsmul, nsmul]
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry
-- A much more important issue is that we now have two module structures over the ring ``ℤ``
-- for ``ℤ`` itself: ``abGrpModule ℤ`` since ``ℤ`` is a abelian group, and ``selfModule ℤ`` since
-- ``ℤ`` is a ring. Those two module structure correspond to the same abelian group structure,
-- but it is not obvious that they have the same scalar multiplication. They actually do, but
-- this isn't true by definition, it requires a proof. This is very bad news for the type class
-- instance resolution procedure and will lead to very frustrating failures for users of this
-- hierarchy. When directly asked to find an instance, Lean will pick one, and we can see
-- which one using:

#synth Module ℤ ℤ -- abGrpModule ℤ

-- But in a more indirect context it can happen that Lean infers the one and then gets confused.
-- This situation is known as a bad diamond. This has nothing to do with the diamond operation
-- we used above, it refers to the way one can draw the paths from ``ℤ`` to its ``Module ℤ``
-- going through either ``AddCommGroup ℤ`` or ``Ring ℤ``.
-- 
-- It is important to understand that not all diamonds are bad. In fact there are diamonds everywhere
-- in Mathlib, and also in this chapter. Already at the very beginning we saw one can go
-- from ``Monoid α`` to ``Dia α`` through either ``Semigroup α`` or ``DiaOneClass α`` and
-- thanks to the work done by the ``class`` command, the resulting two ``Dia α`` instances
-- are definitionally equal. In particular a diamond having a ``Prop``-valued class at the bottom
-- cannot be bad since any too proofs of the same statement are definitionally equal.
-- 
-- But the diamond we created with modules is definitely bad. The offending piece is the ``smul``
-- field which is data, not a proof, and we have two constructions that are not definitionally equal.
-- The robust way of fixing this issue is to make sure that going from a rich structure to a
-- poor structure is always done by forgetting data, not by defining data. This well-known pattern
-- as been named "forgetful inheritance" and extensively discussed in
-- https://inria.hal.science/hal-02463336.
-- 
-- In our concrete case, we can modify the definition of ``AddMonoid`` to include a ``nsmul`` data
-- field and some ``Prop``-valued fields ensuring this operation is provably the one we constructed
-- above. Those fields are given default values using ``:=`` after their type in the definition below.
-- Thanks to these default values, most instances would be constructed exactly as with our previous
-- definitions. But in the special case of ``ℤ`` we will be able to provide specific values.

class AddMonoid' (M : Type) extends AddSemigroup M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid' M] : SMul ℕ M := ⟨AddMonoid'.nsmul⟩
-- 
-- Let us check we can still construct a product monoid instance without providing the ``nsmul``
-- related fields.

instance (M N : Type) [AddMonoid' M] [AddMonoid' N] : AddMonoid' (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc := fun a b c ↦ by ext <;> apply add_assoc
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero
-- And now let us handle the special case of ``ℤ`` where we want to build ``nsmul`` using the coercion
-- of ``ℕ`` to ``ℤ`` and the multiplication on ``ℤ``. Note in particular how the proof fields
-- contain more work than in the default value above.

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
-- Let us check we solved our issue. Because Lean already has a definition of scalar multiplication
-- of a natural number and an integer, and we want to make sure our instance is used, we won't use
-- the ``•`` notation but call ``SMul.mul`` and explicitly provide our instance defined above.

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
-- This story then continues with incorporating a ``zsmul`` field into the definition of groups
-- and similar tricks. You are now ready to read the definition of monoids, groups, rings and modules
-- in Mathlib. There are more complicated than what we have seen here, because they are part of a huge
-- hierarchy, but all principles have been explained above.
-- 
-- As an exercise, you can come back to the order relation hierarchy you built above and try
-- to incorporate a type class ``LT`` carrying the Less-Than notation ``<`` and make sure
-- that every preorder comes with a ``<`` which has a default value built from ``≤`` and a
-- ``Prop``-valued field asserting the natural relation between those two comparison operators.
-- -/
-- 
class LT (α : Type) where -- fill it in

class PreOrder (α : Type) extends LE α, LT α where -- fill it in

