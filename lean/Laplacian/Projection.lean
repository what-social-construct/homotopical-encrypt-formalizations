module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

@[expose] public section

/-
  Projection-model Laplacian.

  Paper correspondence:
  - Paper 1 Sections 2--3: the kernel-normalized projection model used for the
    HCP/CVP comparison.
  - This operator is distinct from the true cellular Hodge Laplacian unless
    the stated normalization conditions identify them.

  This file defines the concrete Grassmannian projection model
  `Δ_W = I - P_W` and the identity `Δ_W b = P_{Wᗮ} b`.
-/

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Matrix Real InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Laplacian associated with a subspace W is I - P_W.
    Eigenvalues: 0 (multiplicity k = dim W) and 1 (multiplicity n-k).
    Python: geometry/hodge.py builds Δ from the simplicial complex;
    here we define Δ directly from the orthogonal projection. -/
def laplacian (W : Submodule ℝ (EuclideanSpace ℝ n)) [W.HasOrthogonalProjection] : Matrix n n ℝ :=
  1 - LinearMap.toMatrix (EuclideanSpace.basisFun n ℝ).toBasis (EuclideanSpace.basisFun n ℝ).toBasis
    (W.subtype.comp (Submodule.orthogonalProjection W).toLinearMap)

/-- The Laplacian applied to b is the projection of b onto W⊥.
    This is the core geometric identity: Δ_W b = P_{W⊥} b.
    Python: encrypt() puts message in ker(Δ), noise in im(Δ);
    decrypt = P_harmonic @ ciphertext recovers message. -/
lemma laplacian_apply (W : Submodule ℝ (EuclideanSpace ℝ n)) [W.HasOrthogonalProjection] (b : EuclideanSpace ℝ n) :
  _root_.laplacian W *ᵥ b = (Submodule.orthogonalProjection W.orthogonal) b := by
    unfold _root_.laplacian;
    ext i;
    simp +decide [ Matrix.one_apply, Matrix.mulVec, dotProduct ];
    simp +decide [ LinearMap.toMatrix_apply ];
    have h_star_proj : W.starProjection b i = ∑ x, W.starProjection (EuclideanSpace.single x 1) i * b x := by
      have h_star_proj : W.starProjection b = ∑ x, b x • W.starProjection (EuclideanSpace.single x 1) := by
        have h_expand : b = ∑ x, b x • EuclideanSpace.single x 1 := by
          simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
            ((EuclideanSpace.basisFun n ℝ).sum_repr b).symm
        calc
          W.starProjection b = W.starProjection (∑ x, b x • EuclideanSpace.single x 1) :=
            congrArg W.starProjection h_expand
          _ = ∑ x, b x • W.starProjection (EuclideanSpace.single x 1) := by
            simp only [map_sum, map_smul]
      rw [h_star_proj]
      simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
        Pi.smul_apply, smul_eq_mul, mul_comm]
    simp +decide [ h_star_proj, sub_mul, Finset.sum_sub_distrib ]

end
