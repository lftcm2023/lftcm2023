import LftCM.C12A_Differential_Geometry.Lib
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.Analysis.NormedSpace.Dual

/-!
# Differential Geometry

Acknowledgements: Based on the tutorial by Sébastien Gouëzel at LFTCM 2020.

## An overview of manifolds in Lean, discussing design decisions

What is a manifold?

(1) allow field other than `ℝ` or `ℂ`?
(2) allow infinite dimension?
(3) allow boundary?
(4) allow model space depending on the point of the manifold?

Bourbaki: 2, 4
Lean: 1, 2, 3

Manifold in Lean:

* charted space structure, i.e., set of partial homeomorphisms to a model space.
  This is data, fixed once and for all (and a typeclass)
* compatibility condition, i.e., the change of coordinates should belong to some subgroup
  of the group of partial homeomorphisms of the model space. This is Prop (and a typeclass).
  The same manifold can be at the same time an analytic manifold,
  a smooth manifold and a topological manifold (with the same fixed atlas).
* A charted space is a smooth manifold (with corners) if it is compatible with the smooth
  groupoid on the model space. To cover uniformly both situations with and without boundary,
  the smooth groupoid is with respect to a map `I : H → E` (think of `H` as the half-space and
  `E` the full space) in the half-space situation and `id : E → E` in the boundaryless situation.
  This map `I` is called a _model with corners_. The most standard ones
  (identity in `ℝ^n` and inclusion of half-space in `ℝ^n`) have dedicated notations:
  `𝓡 n` and `𝓡∂ n`.
-/

open Set ENat Manifold Metric FiniteDimensional Bundle Function
attribute [local instance] Real.fact_zero_lt_one

noncomputable section
section examples

section unitInterval
open unitInterval

#check I -- I is notation for the interval [0, 1]

/- the interval [0, 1] is modelled by two charts with model space [0, ∞),
so it is a topological manifold -/
example : ChartedSpace (EuclideanHalfSpace 1) I := by
  infer_instance

/- To state that it is a smooth manifold, we have to say that all coordinate changes
live in the groupoid of smooth maps -/
example : HasGroupoid I (contDiffGroupoid ∞ (𝓡∂ 1)) := by
  infer_instance

-- This is the same as saying that `I` forms a smooth manifold.
example : SmoothManifoldWithCorners (𝓡∂ 1) I := by
  infer_instance

-- atlases are not maximal in general
#check (contDiffGroupoid ∞ (𝓡∂ 1)).maximalAtlas I

end unitInterval

-- the sphere in a finite-dimensional inner product space is a smooth manifold

variable (n : ℕ) (E : Type*) [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)]
#check SmoothManifoldWithCorners (𝓡 n) (sphere (0 : E) 1)

-- the map 𝕊ⁿ ↪ ℝⁿ⁺¹ is smooth
example : Smooth (𝓡 n) 𝓘(ℝ, E) ((·) : sphere (0 : E) 1 → E) := by
  exact?

-- the circle is a Lie group
example : LieGroup (𝓡 1) circle := by
  infer_instance

/- Dicussing three (controversial?) design decisions

#### Partial homeomorphisms

What is a partial homeomorphism `f` between an open subset of `E` and an open subset of `F`?
This is notion is called `LocalHomeomorph` in Mathlib.
(1) a map defined on a Subtype: `f x` only makes sense for `x : f.source`;
(2) a map defined on the whole space `E`, but taking values in `Option F = F ∪ {junk}`,
  with `f x = junk` when `x ∉ f.source`;
(3) a map defined on the whole space `E`, taking values in `F`,
  and we don't care about its values outside of `f.source`.

Just like division by zero! But worse:

* issue with (1): you keep intersecting chart domains.
  But the Subtype `u ∩ v` is not the same as the Subtype `v ∩ u`,
  so you keep adding casts everywhere.
* issue with (2): if you want to say that a chart is smooth,
  then you define to define smooth functions between `Option E` and `Option F`
  when `E` and `F` are vector spaces. All notions need to be redefined with `Option`.
* issue with (3): it works perfectly well, but it makes mathematicians unhappy/uneasy
  (and it is *not* equivalent to (1) or (2) when one of the spaces is empty).

We pick (3) in Mathlib.
-/

#check Equiv -- bijections with a chosen inverse
#check LocalEquiv -- An equiv between a subset of the domain and a subset of the codomain
#check LocalHomeomorph -- A homeomorphism between open subsets of the domain and codomain


/-
#### Tangent vectors

What is a tangent vector (for a manifold `M` modelled on a vector space `E`)?
(1) An equivalence class of germs of curves
(2) A derivation
(3) Physicist point of view: I don't know what a tangent vector is, but I know in charts.
  Mathematician's interpretation: equivalence class of `(e, v)`
  where `e` is a chart at `x`, `v` a vector in the vector space,
  and `(e, v) ∼ (e', v')` if `D(e' ∘ e ⁻¹) v = v'`
(4) ...

Issues:
(1) Pictures are pretty, but this doesn't bring anything compared to (3)
  when you go down to details.
  And what about boundaries, where you can only have a half-curve
(2) Need partitions of unity to show that this is local and coincides with the usual point of view.
  Doesn't work well in finite smoothness, nor in complex manifolds
(3) Fine, works in all situations, but requires a lot of work to define the equivalence classes,
  the topology, check that the topology is compatible with the vector space structure, and so on.
  In a vector space, the tangent space is not defeq to the vector space itself
(4) Pick one favorite chart at `x`, say `e_x`, and *define* the tangent space at `x` to be `E`,
  but "seen" in the chart `e_x` (this will show up in the definition of the derivative: the
  derivative of `f : M → M'` at `x` is defined to be the derivative of the map
  `e_{f x} ∘ f ∘ e_x⁻¹`). Works perfectly fine, but makes mathematicians unhappy/uneasy.

We pick (4) in Mathlib. In fact, in the definition of a manifold,
every point has a preferred chart associated to it.
-/
#check TangentSpace
#check TangentBundle

/-
#### Smooth functions in manifolds with boundary

Usual definition of smooth functions in a half space: extend to a smooth function a little bit
beyond the boundary, so one only really needs to speak of smooth functions in open subsets of
vector spaces.

When you define the derivative, you will need to check that it does not depend on the choice
of the extension. Even worse when you want to define the tangent bundle: choose an open extension
of your manifold with boundary, and then check that the restriction of the tangent bundle does
not depend on the choice of the extension. Very easy when handwaving, nightmare to formalize.
(What is the extension of the manifold with boundary? Another type?)

Instead, if you define derivatives in (non-open) domains, you can talk of smooth functions in
domains, and do everything without extending. Need to know this early enough: when starting to
define derivatives, you should already think of manifolds with boundaries! That's what we did
in mathlib.

Difficulty: if a domain `s` is too small (think `s = ℝ ⊆ ℝ^2`), the values of `f` on `s` do not
prescribe uniquely a derivative, so `fderivWithinAt ℝ f s x` may behave badly: the derivative of
a sum might be different from sum of derivatives, as there is an arbitrary choice to be made.
This does not happen with the half-space, as it is large enough: derivatives within domains only
work well if the tangent directions span the whole space. Predicate `UniqueDiffOn` for sets
in vector spaces. You won't find this in books!
-/
#check ContDiffWithinAt


-- declaring a smooth manifold is a little verbose:

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners 𝕜 F G) {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N]

example (f : M → N) (x : M) : TangentSpace I x →L[𝕜] TangentSpace J (f x) :=
  mfderiv I J f x

example {f g : M → M} (x : M)
    (hg : MDifferentiableAt I I g (f x)) (hf : MDifferentiableAt I I f x) :
    mfderiv I I (g ∘ f) x = (mfderiv I I g (f x)).comp (mfderiv I I f x) :=
  mfderiv_comp x hg hf

example (f : M → N) : TangentBundle I M → TangentBundle J N :=
  tangentMap I J f

example [AddGroup N] [LieAddGroup J N] {f g : M → N} {n : ℕ∞}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (f + g) :=
  hf.add hg

-- We also have smooth vector bundles

#check Trivialization
#check FiberBundle
#check VectorBundle
#check SmoothVectorBundle

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (IB : ModelWithCorners 𝕜 E H) {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  [SmoothManifoldWithCorners IB B]

-- Let `E₁` and `E₂` be smooth vector bundles over `B`

variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B → Type*)
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x : B, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [SmoothVectorBundle F₁ E₁ IB]
variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B → Type*)
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [SmoothVectorBundle F₂ E₂ IB]


-- The product of two bundles is a smooth vector bundle.

example : SmoothVectorBundle (F₁ × F₂) (E₁ ×ᵇ E₂) IB := by
  infer_instance

-- We can take construct the bundle of continuous linear maps between bundles.

variable [∀ x, TopologicalAddGroup (E₁ x)] [∀ x, TopologicalAddGroup (E₂ x)]
  [∀ x, ContinuousSMul 𝕜 (E₂ x)]


example : SmoothVectorBundle (F₁ →L[𝕜] F₂) (Bundle.ContinuousLinearMap (.id 𝕜) E₁ E₂) IB := by
  infer_instance

-- We can pull back vector bundles.

variable (f : C^∞⟮I, M; IB, B⟯)

example : SmoothVectorBundle F₁ ((f : M → B) *ᵖ E₁) I := by
  apply SmoothVectorBundle.pullback

/- Patrick Massot, Oliver Nash and I have proven sphere eversion from Gromov's h-principle -/

def Immersion (f : M → N) : Prop := ∀ m, Injective (mfderiv I J f m)

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 3)]

local notation "ℝ³" => E
local notation "𝕊²" => sphere (0 : ℝ³) 1

theorem sphere_eversion : ∃ f : ℝ → 𝕊² → ℝ³,
    (ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ³) ∞ (uncurry f)) ∧
    (f 0 = λ x : 𝕊² ↦ (x : ℝ³)) ∧
    (f 1 = λ x : 𝕊² ↦ -(x : ℝ³)) ∧
    ∀ t, Immersion (𝓡 2) 𝓘(ℝ, ℝ³) (f t) :=
  sorry -- not yet in mathlib

end examples














/-! ## Exercises -/

/-! ### Local homeomorphisms

Local homeomorphisms are globally defined maps with a globally defined "inverse", but the only
relevant set is the *source*, which should be mapped homeomorphically to the *target*.
-/

-- set up a simple helper simp lemma to simplify our life later.
@[simp] lemma neg_mem_Ioo_minus_one_one (x : ℝ) :
    -x ∈ Ioo (-1 : ℝ) 1 ↔ x ∈ Ioo (-1 : ℝ) 1 := by
  sorry

/- Define a local homeomorphism from `ℝ` to `ℝ` which is just `x ↦ -x`, but on `(-1, 1)`. In
Lean, the interval `(-1, 1)` is denoted by `Ioo (-1 : ℝ) 1` (where `o` stands for _open_). -/

def myFirstLocalHomeo : LocalHomeomorph ℝ ℝ where
  toFun := fun x ↦ -x
  invFun := fun x ↦ -x
  source := Ioo (-1) 1
  target := sorry
  map_source' := by
    sorry
  map_target' := by
    sorry
  left_inv' := by
    sorry
  right_inv' := by
    sorry
  open_source := sorry
  open_target := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry
/- Two simple lemmas that will prove useful below. You can leave them sorried if you like. -/

lemma ne_3_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-1 : ℝ) 1) : x ≠ 3 := by

lemma neg_ne_3_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-1 : ℝ) 1) : -x ≠ 3 := by

/- Now, define a second local homeomorphism which is almost like the previous one.  You may find the
following lemma useful for `continuous_toFun`: -/
#check ContinuousOn.congr


def mySecondLocalHomeo : LocalHomeomorph ℝ ℝ where
  toFun := fun x ↦ if x = 3 then 0 else - x
  invFun := fun x ↦ -x
  source := Ioo (-1) 1
  target := sorry
  map_source' := sorry
  map_target' := sorry
  left_inv' := sorry
  right_inv' := sorry
  open_source := sorry
  open_target := sorry
  continuous_toFun := by
    sorry
  continuous_invFun := sorry

/- Although the two above local homeos are the same for all practical purposes as they coincide
where relevant, they are not *equal*: -/

lemma myFirstLocalHomeo_ne_mySecondLocalHomeo :
    myFirstLocalHomeo ≠ mySecondLocalHomeo := by

/- The right equivalence relation for local homeos is not equality, but `EqOnSource`.
Indeed, the two local homeos we have defined above coincide from this point of view. -/

#check LocalHomeomorph.EqOnSource

lemma EqOnSource_myFirstLocalHomeo_mySecondLocalHomeo :
    myFirstLocalHomeo.EqOnSource mySecondLocalHomeo := by

/-! ### An example of a charted space structure on `ℝ`

A charted space is a topological space together with a set of local homeomorphisms to a model space,
whose sources cover the whole space. For instance, `ℝ` is already endowed with a charted space
structure with model space `ℝ`, where the unique chart is the identity:
-/

#check chartedSpaceSelf ℝ

/- For educational purposes only, we will put another charted space structure on `ℝ` using the
local homeomorphisms we have constructed above. To avoid using too much structure of `ℝ` (and to
avoid confusing Lean), we will work with a copy of `ℝ`, on which we will only register the
topology. -/

def Myℝ : Type := ℝ
deriving OrderedRing, TopologicalSpace

@[simps]
instance chartedSpaceMyℝ : ChartedSpace ℝ Myℝ where
  atlas := { LocalHomeomorph.refl ℝ, myFirstLocalHomeo }
  chartAt := fun x ↦ if x ∈ Ioo (-1) 1 then myFirstLocalHomeo else LocalHomeomorph.refl ℝ
  mem_chart_source := by
  chart_mem_atlas := by


/- Now come more interesting bits. We have endowed `Myℝ` with a charted space structure, with charts
taking values in `ℝ`. We want to say that this is a smooth structure, i.e., the changes of
coordinates are smooth. In Lean, this is written with `has_groupoid`. A groupoid is a set
of local homeomorphisms of the model space (for example, local homeos that are smooth on their
domain). A charted space admits the groupoid as a structure groupoid if all the changes of
coordinates belong to the groupoid.

There is a difficulty that the definitions are set up to be able to also speak of smooth manifolds
with boundary or with corners, so the name of the smooth groupoid on `ℝ` has the slightly strange
name `contDiffGroupoid ∞ (modelWithCornersSelf ℝ ℝ)`. To avoid typing again and again
`modelWithCornersSelf ℝ ℝ`, let us introduce a shortcut
-/

@[reducible]
def 𝓡1 := modelWithCornersSelf ℝ ℝ

/- In the library, there are such shortcuts for manifolds modelled on `ℝ^n`, denoted with `𝓡 n`,
but for `n = 1` this does not coincide with the above one, as `ℝ^1` (a.k.a. `Fin 1 → ℝ`) is not
the same as `ℝ`! Still, since they are of the same nature, the notation we have just introduced
is very close, compare `𝓡1` with `𝓡 1` (and try not to get confused): -/

instance smooth_Myℝ : HasGroupoid Myℝ (contDiffGroupoid ∞ 𝓡1) := by
  -- in theory, we should prove that all compositions of charts are diffeos, i.e., they are smooth
  -- and their inverse are smooth. For symmetry reasons, it suffices to check one direction
  apply hasGroupoid_of_pregroupoid
  dsimp only
  -- take two charts `e` and `e'`
  intro e e' he he'
  simp [atlas] at he he' ⊢
  -- to continue, some hints:
  -- (1) don't hesitate to use the fact that the restriction of a smooth function to a
  -- subset is still smooth there (`ContDiff.contDiffOn`)
  -- (2) hopefully, there is a theorem saying that the negation function is smooth.
  -- you can either try to guess its name, or hope that `apply?` will help you there.


/- The statement of the previous instance is not very readable. There is a shortcut notation: -/

instance : SmoothManifoldWithCorners 𝓡1 Myℝ := { smooth_Myℝ with }

/- We will now study a very simple map from `Myℝ` to `ℝ`, the identity. -/
def myMap : Myℝ → ℝ := fun x ↦ x

/- The map `myMap` is a map going from the type `Myℝ` to the type `ℝ`. From the point of view of
the kernel of Lean, it is just the identity, but from the point of view of structures on `Myℝ`
and `ℝ` it might not be trivial, as we have registered different instances on these two types. -/

/- The continuity should be trivial, as the topologies on `Myℝ` and `ℝ` are definitionally the
same. So `continuous_id` might help. -/

lemma continuous_myMap : Continuous myMap := by


/- Smoothness should not be obvious, though, as the manifold structures are not the same: the atlas
on `Myℝ` has two elements, while the atlas on `ℝ` has one single element.
Note that `Myℝ` is not a vector space, nor a normed space, so one can not ask whether `myMap`
is smooth in the usual sense (as a map between vector spaces): -/

-- lemma contDiff_myMap : ContDiff ℝ ∞ myMap := sorry

/- does not make sense (try uncommenting it!) However, we can ask whether `myMap` is a smooth
map between manifolds, i.e., whether it is smooth when read in the charts. When we mention the
smoothness of a map, we should always specify explicitly the model with corners we are using,
because there might be several around (think of a complex manifold that you may want to consider
as a real manifold, to talk about functions which are real-smooth but not holomorphic) -/

lemma contMDiff_myMap : ContMDiff 𝓡1 𝓡1 ∞ myMap := by
  -- put things in a nicer form. The simp-set `mfld_simps` registers many simplification rules for
  -- manifolds. `simp` is used heavily in manifold files to bring everything into manageable form.
  rw [contMDiff_iff]
  simp only [continuous_myMap, mfld_simps]
  -- simp has erased the chart in the target, as it knows that the only chart in the manifold `ℝ`
  -- is the identity.
  intro x

/- Now, let's go to tangent bundles. We have a smooth manifold, so its tangent bundle should also
be a smooth manifold. -/

-- the type `TangentBundle 𝓡1 Myℝ` makes sense
#check TangentBundle 𝓡1 Myℝ

/- The tangent space above a point of `Myℝ` is just a one-dimensional vector space
(identified with `ℝ`).
So, one can prescribe an element of the tangent bundle as a pair (more on this below) -/
example : TangentBundle 𝓡1 Myℝ := ⟨(4 : ℝ), 0⟩

/- Type-class inference can construct the smooth manifold structure on the tangent bundle. -/
example : SmoothManifoldWithCorners (𝓡1.prod 𝓡1) (TangentBundle 𝓡1 Myℝ) := by

/-
NB: the model space for the tangent bundle to a product manifold or a tangent space is not
`ℝ × ℝ`, but a copy called `ModelProd ℝ ℝ`. Otherwise, `ℝ × ℝ` would have two charted space
structures with model `ℝ × ℝ`, the identity one and the product one, which are not definitionally
equal. And this would be bad.
-/
example : ChartedSpace (ModelProd ℝ ℝ) (TangentBundle 𝓡1 Myℝ) := by

/-
The charts of any smooth vector bundle are characterized by `FiberBundle.chartedSpace_chartAt`
-/
#check @FiberBundle.chartedSpace_chartAt

/- A smooth map between manifolds induces a map between their tangent bundles. In `mathlib` this is
called the `tangentMap` (you might instead know it as the "differential" or "pushforward" of the
map).  Let us check that the `tangentMap` of `myMap` is smooth. -/
lemma ContMDiff_tangentMap_myMap :
  ContMDiff (𝓡1.prod 𝓡1) (𝓡1.prod 𝓡1) ∞ (tangentMap 𝓡1 𝓡1 myMap) := by
  -- hopefully, there is a theorem providing the general result, i.e. the tangent map to a smooth
  -- map is smooth.
  -- you can either try to guess its name, or hope that `apply?` will help you there.

/- (Harder question) Can you show that this tangent bundle is homeomorphic to `ℝ × ℝ`? You could
try to build the homeomorphism by hand, using `tangentMap 𝓡1 𝓡1 myMap` in one direction and a
similar map in the other direction, but it is probably more efficient to use one of the charts of
the tangent bundle.

Remember, the model space for `TangentBundle 𝓡1 Myℝ` is `ModelProd ℝ ℝ`, not `ℝ × ℝ`. But the
topologies on `ModelProd ℝ ℝ` and `ℝ × ℝ` are the same, so it is by definition good enough to
construct a homeomorphism with `ModelProd ℝ ℝ`.
 -/

def myHomeo : TangentBundle 𝓡1 Myℝ ≃ₜ (ℝ × ℝ) := by

/- Up to now, we have never used the definition of the tangent bundle, and this corresponds to
the usual mathematical practice: one doesn't care if the tangent space is defined using germs of
curves, or spaces of derivations, or whatever equivalent definition. Instead, one relies all the
time on functoriality (i.e., a smooth map has a well defined derivative, and they compose well,
together with the fact that the tangent bundle to a vector space is the product).

If you want to know more about the internals of the tangent bundle in mathlib, you can browse
through the next section, but it is maybe wiser to skip it on first reading, as it is not needed
to use the library
-/

section you_should_probably_skip_this

/- If `M` is a manifold modelled on a vector space `E`, then tangent bundle is defined as
  `TotalSpace E (TangentSpace I : M → Type _)`. An element of this is a pair `⟨x, v⟩` with `x : M`
  and `v : TangentSpace I x`.
  Here `TangentSpace I x` is just (a copy of) `E` by definition. -/

lemma tangentBundle_myℝ_eq_totalSpace :
    TangentBundle 𝓡1 Myℝ = Bundle.TotalSpace ℝ (fun _x : Myℝ ↦ ℝ) :=
  rfl

/- However, in general, a tangent bundle is not trivial:
the topology on `TangentBundle 𝓡1 Myℝ` is *not* the product topology.
Instead, the tangent space at a point `x` is identified
with `ℝ` through some preferred chart at `x`, called `chartAt ℝ x`,
but the way they are glued together depends on the manifold and the charts.

In vector spaces, the tangent space is canonically the product space, with the same topology, as
there is only one chart so there is no strange gluing at play. The fact that the canonical map
from the sigma type to the product type (called `equiv.sigma_equiv_prod`) is a homeomorphism is
given in the library by `tangentBundleModelSpaceHomeomorph` (note that this is a definition,
constructing the homeomorphism, instead of a proposition asserting that `equiv.sigma_equiv_prod`
is a homeomorphism, because we use bundled homeomorphisms in mathlib).

Let us register the identification explicitly, as a homeomorphism. You can use the relevant fields
of `tangentBundleModelSpaceHomeomorph` to fill the nontrivial fields here.
-/

def tangentBundleVectorSpaceTriv (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E] :
  TangentBundle (modelWithCornersSelf ℝ E) E ≃ₜ E × E where
  toFun := fun p ↦ (p.1, p.2)
  invFun := fun p ↦ ⟨p.1, p.2⟩
  left_inv := by
  right_inv := by
  continuous_toFun := by
  continuous_invFun := by

/- Even though the tangent bundle to `Myℝ` is trivial abstractly, with this construction the
tangent bundle is *not* the product space with the product topology, as we have used various charts
so the gluing is not trivial. The following exercise unfolds the definition to see what is going on.
It is not a reasonable exercise, in the sense that one should never ever do this when working
with a manifold! -/

lemma crazy_formula_after_identifications (x : ℝ) (v : ℝ) :
    let p : TangentBundle 𝓡1 Myℝ := ⟨(3 : ℝ), 0⟩
    chartAt (ModelProd ℝ ℝ) p ⟨x, v⟩ = if x ∈ Ioo (-1 : ℝ) 1 then (x, -v) else (x, v) := by
  -- this exercise is not easy (and shouldn't be: you are not supposed to use the library like this!)
  -- if you really want to do this, you should unfold as much as you can using simp and dsimp, until you
  -- are left with a statement speaking of derivatives of real functions, without any manifold code left.

end you_should_probably_skip_this

/-!
### The language of manifolds

In this paragraph, we will try to write down interesting statements of theorems, without proving them. The
goal here is that Lean should not complain on the statement, but the proof should be sorried.
-/

/- Here is a first example, already filled up, to show you how diffeomorphisms are currently named
(we will probably introduce an abbreviation, but this hasn't been done yet).
Don't try to fill the sorried proof! -/

/-- Two zero-dimensional connected manifolds are diffeomorphic. -/
theorem diffeomorph_of_zero_dim_connected
  (M M' : Type*) [TopologicalSpace M] [TopologicalSpace M']
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M']
  [ConnectedSpace M] [ConnectedSpace M'] :
  Nonempty (Structomorph (contDiffGroupoid ∞ (𝓡 0)) M M') :=
sorry

/- Do you think that this statement is correct? (note that we have not assumed that our manifolds
are smooth, nor that they are separated, but this is maybe automatic in zero dimension).

Now, write down a version of this theorem in dimension 1, replacing the first sorry with meaningful content
(and adding what is needed before the colon).
Don't try to fill the sorried proof! -/

/-- Two one-dimensional smooth compact connected manifolds are diffeomorphic. -/
theorem diffeomorph_of_one_dim_compact_connected :
    sorry :=
  sorry

/- You will definitely need to require smoothness and separation in this case, as it is wrong otherwise.
Note that Lean won't complain if you don't put these assumptions, as the theorem would still make
sense, but it would just turn out to be wrong.

The previous statement is not really satisfactory: we would instead like to express that any such
manifold is diffeomorphic to the circle. The trouble is that we don't have the circle as a smooth
manifold yet. Since we have cheated and introduced it (with sorries) at the beginning of the tutorial,
let's cheat again and use it to reformulate the previous statement.
-/

notation "sphere" n => Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1

-- The sphere is connected, compact and Hausdorff:

instance (n : ℕ) : ConnectedSpace (sphere (n+1)) := by
  apply Subtype.connectedSpace
  apply isConnected_sphere
  · simp [← finrank_eq_rank]
    norm_cast
    simp
  · exact zero_le_one

example (n : ℕ) : T2Space (sphere n) := by
  infer_instance

example (n : ℕ) : CompactSpace (sphere n) := by
  infer_instance

instance (n : ℕ) : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n + 1) := by
  constructor
  simp_rw [finrank_euclideanSpace, Fintype.card_fin]

/- Now, you can prove that any one-dimensional compact connected manifold is diffeomorphic to
the circle. Here, you should fill the `sorry` (but luckily you may use
`diffeomorph_of_one_dim_compact_connected`). -/
theorem diffeomorph_circle_of_one_dim_compact_connected
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
    [ConnectedSpace M] [CompactSpace M] [T2Space M] [SmoothManifoldWithCorners (𝓡 1) M] :
    Nonempty (Structomorph (contDiffGroupoid ∞ (𝓡 1)) M (sphere 1)) := by
  exact diffeomorph_of_one_dim_compact_connected M (sphere 1)


/- What about trying to say that there are uncountably many different smooth structures on `ℝ⁴`?
(see https://en.wikipedia.org/wiki/Exotic_R4). The library is not really designed with this in mind,
as in general we only work with one differentiable structure on a space, but it is perfectly
capable of expressing this fact if one uses the `@` version of some definitions.

Don't try to fill the sorried proof!
-/
theorem exotic_ℝ4 :
    sorry :=
  sorry

/-!
### Smooth functions on `[0, 1]`

In the following exercises we will prove that the tangent bundle to `[0, 1]`
is homeomorphic to `[0, 1] × ℝ`. This is math-trivial but Lean-nontrivial.
These facts should also be Lean-trivial, but they are not (yet) since there is essentially
nothing in this direction for now in the library.

The goal is as much to be able to write the statements as to prove them. Most of the necessary vocabulary
has been introduced above, so don't hesitate to browse the file if you are stuck. Additionally, you will
need the notion of a smooth function on a subset: it is `ContDiffOn` for functions between vector
spaces and `ContMDiffOn` for functions between manifolds.

A global advice: don't hesitate to use and abuse `simp`, it is the main workhorse in this
area of mathlib.
-/

open unitInterval


def g : I → ℝ := Subtype.val

-- smoothness results for `EuclideanSpace` are expressed for general `L^p` spaces
-- (as `EuclideanSpace` has the `L^2` norm), in:
#check PiLp.contDiff_coord
#check PiLp.contDiffOn_iff_coord

lemma contMDiffG : ContMDiff (𝓡∂ 1) 𝓡1 ∞ g := by

lemma msmooth_of_smooth {f : ℝ → I} {s : Set ℝ} (h : ContDiffOn ℝ ∞ (fun x ↦ (f x : ℝ)) s) :
  ContMDiffOn 𝓡1 (𝓡∂ 1) ∞ f s := by

/- A function from `ℝ` to `[0,1]` which is the identity on `[0,1]`. -/
def f : ℝ → I :=
  fun x ↦ ⟨max (min x 1) 0, by simp [le_refl, zero_le_one]⟩

lemma contMDiffOnF : ContMDiffOn 𝓡1 (𝓡∂ 1) ∞ f I := by

lemma fog : f ∘ g = id := by

lemma gof : ∀ x ∈ I, g (f x) = x := by

def G : TangentBundle (𝓡∂ 1) I → I × ℝ :=
  fun p ↦ (p.1, ((tangentBundleVectorSpaceTriv ℝ) (tangentMap (𝓡∂ 1) 𝓡1 g p)).2)

lemma continuous_G : Continuous G := by

def F : I × ℝ → TangentBundle (𝓡∂ 1) I :=
  fun p ↦ tangentMapWithin 𝓡1 (𝓡∂ 1) f I ((tangentBundleVectorSpaceTriv ℝ).symm (p.1, p.2))

lemma continuous_F : Continuous F := by

lemma FoG : F ∘ G = id := by

lemma GoF : G ∘ F = id := by

def myTangentHomeo : TangentBundle (𝓡∂ 1) I ≃ₜ I × ℝ := by


/-!
### Further things to do

(1) can you prove `diffeomorph_of_zero_dim_connected`?

(2) Try to express and then prove the local inverse theorem in real manifolds: if a map between
real manifolds (without boundary, modelled on a complete vector space) is smooth, then it is
a local homeomorphism around each point. We already have versions of this statement in mathlib
for functions between vector spaces, but this is very much a work in progress.

(3) What about trying to prove `diffeomorph_of_one_dim_compact_connected`? (I am not sure mathlib
is ready for this, as the proofs I am thinking of are currently a little bit too high-powered.
If you manage to do it, you should absolutely PR it!)

(4) Construct the tensor product of two vector bundles
  Remark: we have not endowed the tensor product of vector spaces with a topology yet,
  even if the vector spaces were finite-dimensional.
-/
