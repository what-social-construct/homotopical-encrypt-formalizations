module

public import Proximity.Application.Projection

@[expose] public section

/-
  Gap-proximity problem vocabulary.

  Paper correspondence:
  - Paper 1 Section 6: near/far proximity promise and calibrated projection
    corollary.
  - Paper 1 appendix ledger: proximity theorem-surface status.

  `Projection.lean` says how a sheaf-side cochain projects to a code/evaluation
  shadow. This file names the near/far decision problem and the end-to-end
  gap obligation needed before a composed projection chain becomes a genuine
  reduction of proximity problems.

  Scope note: this is the concrete-application problem interface. Reed-Solomon list
  decoding and mutual correlated agreement can instantiate this interface only
  after their concrete code family, distance, and gap bounds are supplied.
-/

namespace Hcrypt
namespace Proximity

/-- The output of a promised gap-proximity decision procedure. -/
inductive GapDecision where
  | accept
  | reject
  deriving DecidableEq, Repr

/--
A promised gap-proximity problem.

An instance with `score ≤ nearRadius` should be accepted. An instance with
`farRadius ≤ score` should be rejected. Inputs in the middle are outside the
promise.
-/
structure GapProximityProblem where
  Instance : Type
  score : Instance → ℝ
  nearRadius : ℝ
  farRadius : ℝ
  gap : nearRadius ≤ farRadius

namespace GapProximityProblem

/-- The accepting side of the proximity promise. -/
def Near (P : GapProximityProblem) (x : P.Instance) : Prop :=
  P.score x ≤ P.nearRadius

/-- The rejecting side of the proximity promise. -/
def Far (P : GapProximityProblem) (x : P.Instance) : Prop :=
  P.farRadius ≤ P.score x

/-- The promised region of the decision problem. -/
def Promise (P : GapProximityProblem) (x : P.Instance) : Prop :=
  P.Near x ∨ P.Far x

/-- A solver/tester for a gap-proximity problem. -/
abbrev Solver (P : GapProximityProblem) :=
  P.Instance → GapDecision

/-- Correctness contract for a promised gap-proximity solver. -/
def SolverCorrect (P : GapProximityProblem) (solver : P.Solver) : Prop :=
  (∀ x : P.Instance, P.Near x → solver x = GapDecision.accept)
    ∧ (∀ x : P.Instance, P.Far x → solver x = GapDecision.reject)

end GapProximityProblem

/--
A reduction of promised gap-proximity problems.

It maps near instances to near instances and far instances to far instances.
Therefore any correct solver for the target gives a correct solver for the
source by precomposition.
-/
structure GapReduction (P Q : GapProximityProblem) where
  map : P.Instance → Q.Instance
  preservesNear : ∀ x : P.Instance, P.Near x → Q.Near (map x)
  preservesFar : ∀ x : P.Instance, P.Far x → Q.Far (map x)

namespace GapReduction

/-- Pull a target solver back along a gap reduction. -/
def pullbackSolver {P Q : GapProximityProblem}
    (ρ : GapReduction P Q)
    (solver : Q.Solver) :
    P.Solver :=
  fun x => solver (ρ.map x)

/-- Correct target solvers pull back to correct source solvers. -/
theorem pullbackSolverCorrect {P Q : GapProximityProblem}
    (ρ : GapReduction P Q)
    (solver : Q.Solver)
    (hsolver : Q.SolverCorrect solver) :
    P.SolverCorrect (ρ.pullbackSolver solver) := by
  constructor
  · intro x hx
    exact hsolver.1 (ρ.map x) (ρ.preservesNear x hx)
  · intro x hx
    exact hsolver.2 (ρ.map x) (ρ.preservesFar x hx)

end GapReduction

/-- The sheaf-side gap problem induced by a proximity instance. -/
def sheafGapProblem
    (S : SheafProximityInstance)
    (nearRadius farRadius : ℝ)
    (hgap : nearRadius ≤ farRadius) :
    GapProximityProblem where
  Instance := S.Cochain
  score := S.disagreement
  nearRadius := nearRadius
  farRadius := farRadius
  gap := hgap

/-- The code-shadow gap problem induced by a code/evaluation shadow. -/
def codeGapProblem
    (C : CodeShadow)
    (nearRadius farRadius : ℝ)
    (hgap : nearRadius ≤ farRadius) :
    GapProximityProblem where
  Instance := C.Word
  score := C.distanceToCode
  nearRadius := nearRadius
  farRadius := farRadius
  gap := hgap

/--
An end-to-end gap projection.

`EvaluationProjection` records the composed map into the final code/evaluation
shadow. The extra `preservesFar` field is intentionally an end-of-chain
obligation: intermediate projections may collapse intended quotient directions,
but the calibrated composed map must preserve the promised far side.
-/
structure EndToEndGapProjection
    (S : SheafProximityInstance)
    (C : CodeShadow)
    (nearRadius farRadius : ℝ) where
  projection : EvaluationProjection S C
  preservesFar :
    ∀ c : S.Cochain,
      farRadius ≤ S.disagreement c →
      farRadius ≤ C.distanceToCode (projection.map c)

namespace EndToEndGapProjection

/-- An end-to-end gap projection is a reduction to the code shadow. -/
def toGapReduction
    {S : SheafProximityInstance} {C : CodeShadow}
    {nearRadius farRadius : ℝ}
    (γ : EndToEndGapProjection S C nearRadius farRadius)
    (hgap : nearRadius ≤ farRadius) :
    GapReduction
      (sheafGapProblem S nearRadius farRadius hgap)
      (codeGapProblem C nearRadius farRadius hgap) where
  map := γ.projection.map
  preservesNear := by
    intro c hc
    exact le_trans (γ.projection.distanceControlled c) hc
  preservesFar := by
    intro c hc
    exact γ.preservesFar c hc

/--
A correct code-shadow gap solver gives a correct sheaf-side gap solver whenever
the composed projection chain preserves the calibrated end-to-end gap.
-/
theorem pullback_code_solver_correct
    {S : SheafProximityInstance} {C : CodeShadow}
    {nearRadius farRadius : ℝ}
    (γ : EndToEndGapProjection S C nearRadius farRadius)
    (hgap : nearRadius ≤ farRadius)
    (solver : (codeGapProblem C nearRadius farRadius hgap).Solver)
    (hsolver :
      (codeGapProblem C nearRadius farRadius hgap).SolverCorrect solver) :
    (sheafGapProblem S nearRadius farRadius hgap).SolverCorrect
      ((γ.toGapReduction hgap).pullbackSolver solver) :=
  GapReduction.pullbackSolverCorrect (γ.toGapReduction hgap) solver hsolver

end EndToEndGapProjection

/--
A calibrated end-to-end gap projection.

Unlike `EndToEndGapProjection`, the source and target gap radii may differ.
This is the better interface for lossy projection chains: the near side is
controlled by an explicit radius comparison, while the far side is the final
non-collapse theorem for the composed map.
-/
structure CalibratedEndToEndGapProjection
    (S : SheafProximityInstance)
    (C : CodeShadow)
    (sourceNearRadius sourceFarRadius targetNearRadius targetFarRadius : ℝ) where
  projection : EvaluationProjection S C
  nearRadiusCompatible : sourceNearRadius ≤ targetNearRadius
  preservesFar :
    ∀ c : S.Cochain,
      sourceFarRadius ≤ S.disagreement c →
      targetFarRadius ≤ C.distanceToCode (projection.map c)

namespace CalibratedEndToEndGapProjection

/-- A calibrated end-to-end projection is a reduction between calibrated gap problems. -/
def toGapReduction
    {S : SheafProximityInstance} {C : CodeShadow}
    {sourceNearRadius sourceFarRadius targetNearRadius targetFarRadius : ℝ}
    (γ :
      CalibratedEndToEndGapProjection
        S C sourceNearRadius sourceFarRadius targetNearRadius targetFarRadius)
    (hsource : sourceNearRadius ≤ sourceFarRadius)
    (htarget : targetNearRadius ≤ targetFarRadius) :
    GapReduction
      (sheafGapProblem S sourceNearRadius sourceFarRadius hsource)
      (codeGapProblem C targetNearRadius targetFarRadius htarget) where
  map := γ.projection.map
  preservesNear := by
    intro c hc
    exact le_trans (le_trans (γ.projection.distanceControlled c) hc) γ.nearRadiusCompatible
  preservesFar := by
    intro c hc
    exact γ.preservesFar c hc

/--
A correct target solver pulls back through a calibrated end-to-end projection.
-/
theorem pullback_code_solver_correct
    {S : SheafProximityInstance} {C : CodeShadow}
    {sourceNearRadius sourceFarRadius targetNearRadius targetFarRadius : ℝ}
    (γ :
      CalibratedEndToEndGapProjection
        S C sourceNearRadius sourceFarRadius targetNearRadius targetFarRadius)
    (hsource : sourceNearRadius ≤ sourceFarRadius)
    (htarget : targetNearRadius ≤ targetFarRadius)
    (solver : (codeGapProblem C targetNearRadius targetFarRadius htarget).Solver)
    (hsolver :
      (codeGapProblem C targetNearRadius targetFarRadius htarget).SolverCorrect solver) :
    (sheafGapProblem S sourceNearRadius sourceFarRadius hsource).SolverCorrect
      ((γ.toGapReduction hsource htarget).pullbackSolver solver) :=
  GapReduction.pullbackSolverCorrect (γ.toGapReduction hsource htarget) solver hsolver

end CalibratedEndToEndGapProjection

namespace EndToEndGapProjection

/-- A same-radius end-to-end projection is a calibrated projection. -/
def toCalibrated
    {S : SheafProximityInstance} {C : CodeShadow}
    {nearRadius farRadius : ℝ}
    (γ : EndToEndGapProjection S C nearRadius farRadius) :
    CalibratedEndToEndGapProjection
      S C nearRadius farRadius nearRadius farRadius where
  projection := γ.projection
  nearRadiusCompatible := le_rfl
  preservesFar := γ.preservesFar

end EndToEndGapProjection

/--
Projected far-ness reflects back to sheaf far-ness automatically.

This is useful for audits: if the projected code/evaluation shadow is already
far from code, then the source cochain was at least that far from the sheaf-side
global-section condition.
-/
theorem sheaf_far_of_projected_far
    {S : SheafProximityInstance} {C : CodeShadow}
    (η : EvaluationProjection S C)
    (c : S.Cochain)
    {farRadius : ℝ}
    (hfar : farRadius ≤ C.distanceToCode (η.map c)) :
    farRadius ≤ S.disagreement c :=
  le_trans hfar (η.distanceControlled c)

end Proximity
end Hcrypt
