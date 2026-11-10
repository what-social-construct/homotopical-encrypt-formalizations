module

public import Proximity.Concrete.Grassmannian
public import Laplacian.Grassmannian.SearchSpace
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

@[expose] public section

/-
  Grassmannian-to-Plucker bridge.

  Paper correspondence:
  - Paper 1 Section 6: hidden Grassmannian source to public Plucker shadow.

  This file records the bridge from the projection-facing Hodge/Grassmannian
  model to Plucker-coordinate public shadows. The concrete coordinate layer uses
  an explicit frame witness for a rank-`r` harmonic subspace and maps it into
  the actual exterior power. Basis/frame invariance is kept as an obligation
  because it is exactly the proof needed to make the public shadow independent
  of the private frame choice.
-/

namespace Hcrypt
namespace Proximity
namespace GrassmannianPlucker

open scoped BigOperators Real Nat Classical Pointwise
open Matrix Real InnerProductSpace

set_option linter.mathlibStandardSet false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

variable {n : Type} [Fintype n] [DecidableEq n]

/--
Projection-facing Grassmannian point used by the Laplacian/Hodge/proximity path.

This is the subspace convention: a rank-`r` harmonic subspace `W`, with
`Δ_W = I - P_W`.
-/
abbrev HarmonicGrassmannianPoint (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) :=
  HarmonicSubspace n r

/-- The actual exterior-power carrier for Plucker coordinates. -/
abbrev ExteriorCoordinate (n : Type) [Fintype n] (r : ℕ) :=
  ⋀[ℝ]^r (EuclideanSpace ℝ n)

/--
A private frame witness for the operative Grassmannian submodule.

The public Plucker coordinate comes from `frame` via `exteriorPower.ιMulti`.
The witness also records that the frame is a basis-like presentation of the
submodule used by the Hodge/proximity layer.
-/
structure FrameWitness (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) where
  point : HarmonicGrassmannianPoint n r
  frame : Fin r → EuclideanSpace ℝ n
  frame_mem : ∀ i : Fin r, frame i ∈ point.carrier
  independent : LinearIndependent ℝ frame
  spans_submodule : Submodule.span ℝ (Set.range frame) = point.carrier

namespace FrameWitness

variable {r : ℕ}

/-- The concrete Plucker/exterior-power coordinate induced by the frame witness. -/
def toExterior (W : FrameWitness n r) : ExteriorCoordinate n r :=
  exteriorPower.ιMulti ℝ r W.frame

/-- Coordinates that are explicitly a single exterior product of an `r`-frame. -/
def Decomposable (c : ExteriorCoordinate n r) : Prop :=
  ∃ frame : Fin r → EuclideanSpace ℝ n,
    c = exteriorPower.ιMulti ℝ r frame

/-- The frame-witness Plucker coordinate is decomposable by construction. -/
theorem toExterior_decomposable (W : FrameWitness n r) :
    Decomposable W.toExterior :=
  ⟨W.frame, rfl⟩

/-- The frame witness presents the same submodule used by the Hodge layer. -/
theorem span_eq_hodgeSubmodule (W : FrameWitness n r) :
    Submodule.span ℝ (Set.range W.frame) = W.point.carrier :=
  W.spans_submodule

/-- Every vector in the frame lies in the operative Hodge submodule. -/
theorem frame_mem_hodgeSubmodule (W : FrameWitness n r) :
    ∀ i : Fin r, W.frame i ∈ W.point.carrier :=
  W.frame_mem

end FrameWitness

/--
Concrete Plucker shadow system for frame witnesses.

`Coordinate` is no longer opaque here: it is `⋀[ℝ]^r (EuclideanSpace ℝ n)`.
The remaining predicates capture the algebraic/projective facts needed before
the coordinate can safely become a public chain-facing shadow.
-/
structure FramedSystem (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) where
  Shadow : Type
  normalize : ExteriorCoordinate n r → Shadow
  /-- Exterior coordinate is nonzero, typically from frame independence. -/
  Nonzero : ExteriorCoordinate n r → Prop
  /-- Exterior coordinate satisfies the selected Plucker-relation presentation. -/
  PluckerRelations : ExteriorCoordinate n r → Prop
  /-- Normalized/projective representative is well formed. -/
  Normalized : Shadow → Prop
  /-- Coordinate support/minor pattern is admissible for the chosen regime. -/
  SupportAdmissible : Shadow → Prop
  /-- Projective sign/scale ambiguity between frame choices for the same point. -/
  ProjectivelyEquivalent : ExteriorCoordinate n r → ExteriorCoordinate n r → Prop

namespace FramedSystem

variable {r : ℕ}

/-- Public shadow obtained from an explicit frame witness. -/
def publicShadow (P : FramedSystem n r) (W : FrameWitness n r) :
    P.Shadow :=
  P.normalize W.toExterior

/-- Raw coordinate validity for an explicit frame witness. -/
def ValidRawCoordinate (P : FramedSystem n r) (W : FrameWitness n r) :
    Prop :=
  P.Nonzero W.toExterior
    ∧ FrameWitness.Decomposable W.toExterior
    ∧ P.PluckerRelations W.toExterior

/-- Public shadow validity for an explicit frame witness. -/
def ValidShadow (P : FramedSystem n r) (W : FrameWitness n r) :
    Prop :=
  P.Normalized (P.publicShadow W) ∧ P.SupportAdmissible (P.publicShadow W)

/--
Frame-level soundness obligations.

Decomposability is proved from the exterior-product construction, so it is not
an assumption here. Nonzero, Plucker relations, normalization, and projective
frame-change invariance are the remaining algebraic obligations.
-/
structure Sound (P : FramedSystem n r) : Prop where
  nonzero : ∀ W : FrameWitness n r, P.Nonzero W.toExterior
  pluckerRelations : ∀ W : FrameWitness n r, P.PluckerRelations W.toExterior
  valid_shadow : ∀ W : FrameWitness n r, P.ValidShadow W
  projective_frame_invariance :
    ∀ W V : FrameWitness n r,
      W.point = V.point →
        P.ProjectivelyEquivalent W.toExterior V.toExterior
  projective_invariance :
    ∀ c d : ExteriorCoordinate n r,
      P.ProjectivelyEquivalent c d → P.normalize c = P.normalize d

/-- A sound framed system supplies raw coordinate validity. -/
theorem validRawCoordinate_of_sound
    {P : FramedSystem n r}
    (hP : P.Sound)
    (W : FrameWitness n r) :
    P.ValidRawCoordinate W :=
  ⟨hP.nonzero W, FrameWitness.toExterior_decomposable W, hP.pluckerRelations W⟩

/-- A sound framed system supplies public shadow validity. -/
theorem validShadow_of_sound
    {P : FramedSystem n r}
    (hP : P.Sound)
    (W : FrameWitness n r) :
    P.ValidShadow W :=
  hP.valid_shadow W

/--
Changing the private frame for the same Grassmannian point does not change the
normalized public shadow.
-/
theorem publicShadow_eq_of_same_point
    {P : FramedSystem n r}
    (hP : P.Sound)
    {W V : FrameWitness n r}
    (hWV : W.point = V.point) :
    P.publicShadow W = P.publicShadow V :=
  hP.projective_invariance W.toExterior V.toExterior
    (hP.projective_frame_invariance W V hWV)

end FramedSystem

end

end GrassmannianPlucker
end Proximity
end Hcrypt
