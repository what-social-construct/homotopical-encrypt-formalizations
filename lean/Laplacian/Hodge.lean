module

public import Laplacian.Projection

@[expose] public section

/-
  Hodge-facing Laplacian interface.

  Paper correspondence:
  - Paper 1 Section 2: HCP harmonic projection and residual model.
  - Paper 1 Section 3: Hodge projection as CVP comparison surface.

  `Laplacian.Projection` defines the concrete Grassmannian model
  `Δ_W = I - P_W`. This file names the Hodge/proximity-facing operations
  derived from that model:

    harmonic projection     P_W b
    residual vector         Δ_W b = P_{Wᗮ} b
    residual score          ‖Δ_W b‖

  No new cochain carrier is introduced here. These are projection/residual views
  over the existing ambient cochain vector.
-/

namespace Hcrypt
namespace Laplacian

open scoped BigOperators Real Nat Classical Pointwise
open Matrix Real InnerProductSpace

set_option linter.mathlibStandardSet false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The harmonic/global component of a cochain/vector. -/
def harmonicProjection
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n :=
  (Submodule.orthogonalProjection W) b

/-- The harmonic projection lands in the harmonic subspace. -/
theorem harmonicProjection_mem
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : EuclideanSpace ℝ n) :
    harmonicProjection W b ∈ W := by
  unfold harmonicProjection
  exact (Submodule.orthogonalProjection W b).property

/-- The residual/non-harmonic component detected by `Δ_W`. -/
def residualVector
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n :=
  WithLp.toLp 2 (_root_.laplacian W *ᵥ b)

/-- The Hodge/Laplacian disagreement score. -/
def residual
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : EuclideanSpace ℝ n) : ℝ :=
  ‖residualVector W b‖

/-- Harmonicity as zero Laplacian residual. -/
def IsHarmonic
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : EuclideanSpace ℝ n) : Prop :=
  residualVector W b = 0

/-- The residual vector is the orthogonal projection to `Wᗮ`. -/
theorem residualVector_eq_orthogonalProjection
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : EuclideanSpace ℝ n) :
    residualVector W b = (Submodule.orthogonalProjection W.orthogonal) b := by
  unfold residualVector
  simpa only [WithLp.toLp_ofLp] using
    congrArg (WithLp.toLp 2) (laplacian_apply W b)

/-- The residual score is the norm of the orthogonal component. -/
theorem residual_eq_orthogonalProjection_norm
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : EuclideanSpace ℝ n) :
    residual W b = ‖(Submodule.orthogonalProjection W.orthogonal) b‖ := by
  unfold residual
  rw [residualVector_eq_orthogonalProjection]
  simp

/-- Residual scores are nonnegative. -/
theorem residual_nonneg
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : EuclideanSpace ℝ n) :
    0 ≤ residual W b :=
  norm_nonneg _

/-- Vectors in the harmonic subspace have zero Laplacian residual. -/
theorem isHarmonic_of_mem
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    {b : EuclideanSpace ℝ n}
    (hb : b ∈ W) :
    IsHarmonic W b := by
  unfold IsHarmonic residualVector
  rw [laplacian_apply]
  rw [Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero]
  · rfl
  · simpa [Submodule.orthogonal_orthogonal] using hb

/-- The harmonic projection is harmonic. -/
theorem harmonicProjection_isHarmonic
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : EuclideanSpace ℝ n) :
    IsHarmonic W (harmonicProjection W b) :=
  isHarmonic_of_mem W (harmonicProjection_mem W b)

/-- Vectors in the harmonic subspace have zero residual score. -/
theorem residual_eq_zero_of_mem
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    {b : EuclideanSpace ℝ n}
    (hb : b ∈ W) :
    residual W b = 0 := by
  unfold residual
  rw [isHarmonic_of_mem W hb]
  simp

/-- Zero residual score is equivalent to zero residual vector. -/
theorem residual_eq_zero_iff_isHarmonic
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : EuclideanSpace ℝ n) :
    residual W b = 0 ↔ IsHarmonic W b := by
  unfold residual IsHarmonic
  constructor
  · intro h
    exact norm_eq_zero.mp h
  · intro h
    rw [h]
    simp

/-- Zero Laplacian residual means membership in the harmonic subspace. -/
theorem mem_of_isHarmonic
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    {b : EuclideanSpace ℝ n}
    (hb : IsHarmonic W b) :
    b ∈ W := by
  unfold IsHarmonic residualVector at hb
  rw [laplacian_apply] at hb
  have hproj : W.orthogonal.orthogonalProjection b = 0 := by
    apply Subtype.ext
    exact hb
  have hbOrth : b ∈ W.orthogonal.orthogonal := by
    exact Submodule.orthogonalProjection_eq_zero_iff.mp hproj
  simpa [Submodule.orthogonal_orthogonal] using hbOrth

/-- Harmonicity is exactly membership in the hidden harmonic subspace. -/
theorem isHarmonic_iff_mem
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : EuclideanSpace ℝ n) :
    IsHarmonic W b ↔ b ∈ W := by
  constructor
  · exact mem_of_isHarmonic W
  · exact isHarmonic_of_mem W

/-- Zero residual score is exactly membership in the harmonic subspace. -/
theorem residual_eq_zero_iff_mem
    (W : Submodule ℝ (EuclideanSpace ℝ n))
    [W.HasOrthogonalProjection]
    (b : EuclideanSpace ℝ n) :
    residual W b = 0 ↔ b ∈ W :=
  (residual_eq_zero_iff_isHarmonic W b).trans (isHarmonic_iff_mem W b)

end

end Laplacian
end Hcrypt
