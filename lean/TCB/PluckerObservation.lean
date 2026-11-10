module

public import HCP
public import Proximity.Concrete.GrassmannianPlucker.Reconstruction

@[expose] public section

/-!
# Full Plucker data and the operative harmonic target

At a fixed ambient inner product, the full projective point reconstructs its
subspace and projector. When that subspace is the operative HCP kernel, the
same data determine the operative harmonic component. This is mathematical
recovery on exact real coordinates, not an encoding, efficient algorithm or
digest inversion theorem. Digest-only observations have a different carrier.
-/

set_option autoImplicit false

noncomputable section

namespace Hcrypt.TCB.PluckerObservation

open Proximity.GrassmannianPlucker
open Proximity.GrassmannianPlucker.Concrete

variable {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

/-- Recovery consumes the full existing projective shadow and the observed vector. -/
def recover (shadow : ProjectiveShadow n r) (b : EuclideanSpace ℝ n) :
    EuclideanSpace ℝ n := recoverHarmonicProjector shadow b

/-- Identification with the operative kernel is the exact hypothesis needed here. -/
theorem recover_eq_operativeHarmonicComponent
    (W : FrameWitness n r) (Δ : Matrix n n ℝ)
    (hkernel : W.point.carrier = HCP.matrixHarmonicSubspace Δ)
    (b : EuclideanSpace ℝ n) :
    recover ((projectiveFramedSystem n r).publicShadow W) b =
      HCP.operativeHarmonicComponent Δ b := by
  change recoverHarmonicProjector (normalizeProjective W.toExterior) b = _
  rw [recoverHarmonicProjector_frame, hkernel]
  rfl

/-- A shared full point cannot retain two distinct operative targets at one vector. -/
theorem operativeHarmonicComponent_eq_of_same_full_shadow
    (W V : FrameWitness n r) (Δ Λ : Matrix n n ℝ)
    (hW : W.point.carrier = HCP.matrixHarmonicSubspace Δ)
    (hV : V.point.carrier = HCP.matrixHarmonicSubspace Λ)
    (hshadow : (projectiveFramedSystem n r).publicShadow W =
      (projectiveFramedSystem n r).publicShadow V)
    (b : EuclideanSpace ℝ n) :
    HCP.operativeHarmonicComponent Δ b = HCP.operativeHarmonicComponent Λ b := by
  rw [← recover_eq_operativeHarmonicComponent W Δ hW b,
    ← recover_eq_operativeHarmonicComponent V Λ hV b, hshadow]

end Hcrypt.TCB.PluckerObservation
