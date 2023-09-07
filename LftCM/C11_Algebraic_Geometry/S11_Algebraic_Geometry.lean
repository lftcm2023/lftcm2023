/-
#  Algebraic Geometry in `Mathlib`

This quick walkthrough highlights the definition of
* `Spec` of a `CommRing`, as a `Scheme`;
* `Proj` of a `GradedAlgebra`, as a `LocallyRingedSpace`
in `Mathlib`.

It is the Lean 4 file completing the presentation on Algebraic Geometry
in "Lean for the Curious Mathematician 2023".

There is also an accompanying exercise sheet containing material related,
but not using, the `AlgebraicGeometry` library of `Mathlib`.
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

noncomputable section Spec_and_Proj

open  AlgebraicGeometry Scheme -- self-explanatory?
      CommRingCat  -- the Category of Commutative Rings
      Opposite     --  Opposite categories

abbrev Spec (R) [CommRing R] := Scheme.Spec.obj (op (of R))

-- The n-dimensional affine space over the field k.
def 𝔸 (k) [Field k] (n : ℕ) : Scheme :=
Spec (MvPolynomial (Fin n) k)

#check 𝔸 ℚ 4   -- 𝔸 ℚ 4 : Scheme

example (k) [Field k] (n : ℕ) : IsAffine (𝔸 k n) := by
  sorry
  --exact?     -- fails, since it does not see through '𝔸'
  --unfold 𝔸   -- now 'exact?' works
  --exact SpecIsAffine (op (of (MvPolynomial (Fin n) k)))

/--  A quick definition of $k$-valued points -/
def k_valued_points (k) [Field k] (X : Scheme) :=
Spec k ⟶ X  --  ← is an arrow in the Scheme category,
              --  not a 'usual' function!

variable {k} [Field k] {R} [CommRing R]

example (f : R →+* k) : k_valued_points k (Spec R) := by
  change of R ⟶ of k at f
  exact (specMap f)

/-
###  Projective schemes (as locally ringed spaces)
-/

variable {A : Type*} [CommRing A] [Algebra R A]

variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

def P : LocallyRingedSpace := Proj.toLocallyRingedSpace 𝒜

#check P 𝒜   -- P 𝒜 : LocallyRingedSpace

end Spec_and_Proj
