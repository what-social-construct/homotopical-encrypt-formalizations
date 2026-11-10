module

public import Proximity.Application.Problem
public import Laplacian.Hodge

@[expose] public section

/-
  Grassmannian proximity instance.

  Paper correspondence:
  - Paper 1 Section 6: source-side proximity instance before Plucker shadow.

  This is the first concrete instantiation of the generic proximity interface:
  a hidden harmonic subspace `W` determines a Laplacian `Δ_W = I - P_W`, and
  the sheaf-side disagreement of a cochain/vector `b` is the norm of its
  orthogonal component in `Wᗮ`.

  The construction deliberately uses the clean `Laplacian.Projection` spine rather
  than the broader Tsirelson adversary layer. The actual residual facts are
  imported through `Laplacian.Hodge`, so this projection layer is built from the
  established Hodge objects instead of redefining them.
-/

namespace Hcrypt
namespace Proximity
namespace Grassmannian

open scoped BigOperators Real Nat Classical Pointwise
open Matrix Real InnerProductSpace

set_option linter.mathlibStandardSet false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

variable {n : Type} [Fintype n] [DecidableEq n]

/-- A Grassmannian cochain is a vector in the ambient stalk/cochain space. -/
abbrev GrassmannianCochain (n : Type*) [Fintype n] :=
  EuclideanSpace ℝ n

/-- A vector is a global/harmonic section exactly when it lies in `W`. -/
def GlobalSection
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    (b : GrassmannianCochain n) : Prop :=
  b ∈ W

/--
Geometric disagreement from the hidden harmonic subspace.

This is the L2 norm of the orthogonal component, i.e. the distance from `b` to
`W` in the projection model. For `Δ_W = I - P_W`, `laplacian_apply` identifies
this with the norm of the Laplacian residual.
-/
def disagreement
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : GrassmannianCochain n) : ℝ :=
  ‖(Submodule.orthogonalProjectionOnto W.orthogonal) b‖

/-- The proximity disagreement is exactly the Hodge/Laplacian residual. -/
theorem disagreement_eq_laplacian_residual
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : GrassmannianCochain n) :
    disagreement W b = Hcrypt.Laplacian.residual W b := by
  unfold disagreement Hcrypt.Laplacian.residual
  rw [Hcrypt.Laplacian.residualVector_eq_orthogonalProjection]
  simp

/-- Harmonic/global sections have zero Grassmannian disagreement. -/
theorem disagreement_eq_zero_of_globalSection
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    {b : GrassmannianCochain n}
    (hb : GlobalSection W b) :
    disagreement W b = 0 := by
  unfold disagreement GlobalSection at *
  rw [Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal]
  · simp
  · simpa [Submodule.orthogonal_orthogonal] using hb

/-- Zero Grassmannian disagreement is exactly the global/harmonic condition. -/
theorem disagreement_eq_zero_iff_globalSection
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : GrassmannianCochain n) :
    disagreement W b = 0 ↔ GlobalSection W b := by
  rw [disagreement_eq_laplacian_residual]
  exact Hcrypt.Laplacian.residual_eq_zero_iff_mem W b

/-- The global-section predicate is the Hodge harmonicity predicate. -/
theorem globalSection_iff_isHarmonic
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : GrassmannianCochain n) :
    GlobalSection W b ↔ Hcrypt.Laplacian.IsHarmonic W b :=
  Iff.symm (Hcrypt.Laplacian.isHarmonic_iff_mem W b)

/-- The Grassmannian hidden-subspace instance of sheaf proximity. -/
def proximityInstance
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection] :
    SheafProximityInstance where
  Cochain := GrassmannianCochain n
  GlobalSection := GlobalSection W
  disagreement := disagreement W

/--
The code/evaluation shadow associated to `W`.

For the first internal bridge this shadow is the same ambient vector space,
with codewords given by the harmonic subspace and distance given by the same
orthogonal residual.
-/
def harmonicCodeShadow
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection] :
    CodeShadow where
  Word := GrassmannianCochain n
  Codeword := GlobalSection W
  distanceToCode := disagreement W

/-- The identity map is the canonical projection to the harmonic code shadow. -/
def identityEvaluationProjection
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection] :
    EvaluationProjection (proximityInstance W) (harmonicCodeShadow W) where
  map := id
  preservesGlobalSections := by
    intro b hb
    exact hb
  distanceControlled := by
    intro b
    exact le_rfl

end

end Grassmannian
end Proximity
end Hcrypt
