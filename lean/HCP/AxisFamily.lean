module

public import Hardness
public import Sheaf.HCPAxisFamily
public import Helfer.CochainModel

@[expose] public section

/-!
# A cellular realization of the hidden harmonic-axis ambiguity

The two representatives here are genuine integral cellular sheaves.  Their
semantic interpretations retain the actual cochain differentials in the
bounded-below real-complex Quillen model category.  The public class is their
actual theory of homology-nontriviality tests.  Equality of those theories is
proved from a cellular chain isometry and homological invariance.

The matrix public projection extends that classifier to all matrices by
returning the theory of an admitted representative when one exists, and the
empty theory otherwise.  It makes no claim about serialized payloads, hashes,
or the full public view of a storage protocol.

At the shared observation with both coordinates one, the two operative targets
are distinct nonzero integral messages.  A separate coordinate unit witnesses
fixed-coordinate nonstabilization and instantiates the existing HCP solver and
explicit-CVP-oracle impossibility theorems.
-/

set_option autoImplicit false

noncomputable section

namespace Hcrypt.HCP.AxisFamily

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open Sheaf.HCPAxisFamily HCPBridge
open scoped CochainComplex.Plus.modelCategoryQuillen

/-- The actual cellular complex, interpreted in the genuine cochain model. -/
def semanticInterpretation (axis : Fin 2) :
    Helfer.Interpretation Helfer.CochainModel.Model Helfer.CochainModel.signature :=
  Helfer.CochainModel.interpretation
    (Helfer.CochainModel.ofSheaf (sheaf axis)).model

/-- The cellular chain isometry induces a typed semantic equivalence. -/
theorem semanticEquivalence :
    Helfer.HomotopyEquivalent (semanticInterpretation 0) (semanticInterpretation 1) :=
  Helfer.CochainModel.equivalent_of_isometricCochainEquiv axisSwap

/-- The public class is a full theory in the selected homological closed fragment. -/
def theory (axis : Fin 2) : Set ℤ :=
  Helfer.ClosedTheory Helfer.CochainModel.semantics (semanticInterpretation axis)

/-- Constancy on this family is a consequence of actual semantic equivalence. -/
theorem theory_zero_eq_one : theory 0 = theory 1 :=
  Helfer.closedTheory_eq Helfer.CochainModel.semantics
    Helfer.CochainModel.closedTestInvariance semanticEquivalence

theorem theory_eq (axis otherAxis : Fin 2) : theory axis = theory otherAxis := by
  fin_cases axis <;> fin_cases otherAxis
  · rfl
  · exact theory_zero_eq_one
  · exact theory_zero_eq_one.symm
  · rfl

/-- Extend the actual admitted-operator classifier without selecting a constant class. -/
def publicProjection : PublicProjection Index ℝ (Set ℤ) := fun Δ =>
  if h : ∃ axis : Fin 2, laplacianMatrix axis = Δ then theory h.choose else ∅

theorem publicProjection_laplacian (axis : Fin 2) :
    publicProjection (laplacianMatrix axis) = theory axis := by
  unfold publicProjection
  rw [dite_eq_left (show ∃ a : Fin 2, laplacianMatrix a = laplacianMatrix axis from
    ⟨axis, rfl⟩)]
  exact theory_eq _ _

/-- Actual cellular matrices and actual closed theories form an HCP realization. -/
def realization :
    Realization Helfer.CochainModel.Model Helfer.CochainModel.signature
      Helfer.CochainModel.semantics (Fin 2) Index ℝ (Set ℤ) where
  interpretation := semanticInterpretation
  laplacian := laplacianMatrix
  classifier := ⟨theory⟩
  publicProjection := publicProjection
  classifyTheory := id
  classifier_factors _ := rfl
  operator_classifier_factors := publicProjection_laplacian

/-- The realized matrix acts by the actual cellular Hodge Laplacian. -/
theorem operatorAction (axis : Fin 2) (b : C1) :
    WithLp.toLp 2 (Matrix.mulVec (realization.laplacian axis) b) =
      (sheaf axis).degreeOneLaplacian b := by
  apply PiLp.ext
  intro i
  exact congrFun (laplacianMatrix_mulVec axis b) i

theorem matrix_harmonic_iff (axis : Fin 2) (b : Index → ℝ) :
    MatrixIsHarmonic (realization.laplacian axis) b ↔
      (sheaf axis).IsHarmonicOneCochain (WithLp.toLp 2 b) := by
  change Matrix.mulVec (realization.laplacian axis) b = 0 ↔
    (sheaf axis).degreeOneLaplacian (WithLp.toLp 2 b) = 0
  rw [← operatorAction]
  constructor
  · intro h
    simp [h]
  · intro h
    exact congrArg WithLp.ofLp h

theorem matrixHarmonicSubspace_eq (axis : Fin 2) :
    HCP.matrixHarmonicSubspace (realization.laplacian axis) =
      (sheaf axis).harmonicOneSubspace := by
  ext b
  exact matrix_harmonic_iff axis b

/-- Operative recovery is the actual cellular harmonic projection, not a surrogate. -/
theorem operativeHarmonicComponent_eq (axis : Fin 2) (b : C1) :
    HCP.operativeHarmonicComponent (realization.laplacian axis) b =
      (sheaf axis).harmonicOneProjection b := by
  change (HCP.matrixHarmonicSubspace _).starProjection b = _
  simp only [matrixHarmonicSubspace_eq]
  rfl

/-- Actual Laplacian naturality and typed semantic equivalence in one package. -/
def isometricPresentation : IsometricPresentationEquivalence realization 0 1 where
  semanticEquivalence := semanticEquivalence
  transport := axisSwap.degreeOne
  laplacian_naturality b := by
    have h : WithLp.toLp 2 (Matrix.mulVec (realization.laplacian 1)
        (axisSwap.degreeOne b)) =
        axisSwap.degreeOne
          (WithLp.toLp 2 (Matrix.mulVec (realization.laplacian 0) b)) := by
      rw [operatorAction, operatorAction]
      exact axisSwap.degreeOneLaplacian_naturality b
    exact congrArg WithLp.ofLp h

/-- A fixed raw coordinate is not stabilized by the private axis swap. -/
def fixedCoordinateNonstabilization :
    FixedCoordinateNonstabilization isometricPresentation where
  input := unitCochain 1
  harmonic_left := by
    rw [matrix_harmonic_iff, harmonic_iff]
    simp
  preimage_not_harmonic_left := by
    rw [matrix_harmonic_iff, harmonic_iff]
    change ¬ (cochainSwap.symm (unitCochain 1)) ⟨(), 0⟩ = 0
    simp [cochainSwap_symm_apply]

/-- The HCP separation witness is constructed from the actual cellular family. -/
def kernelSeparation : KernelSeparationWitness realization :=
  kernelSeparationWitness_of_isometricNonstabilization
    isometricPresentation fixedCoordinateNonstabilization

theorem same_public_class : realization.classifier.π 0 = realization.classifier.π 1 :=
  samePublicClass_of_homotopyEquivalent realization
    Helfer.CochainModel.closedTestInvariance semanticEquivalence

theorem kernel_ambiguous : KernelAmbiguous realization.publicProjection :=
  kernelAmbiguous_of_kernelSeparation realization
    Helfer.CochainModel.closedTestInvariance kernelSeparation

theorem classifier_nonfaithful : Axioms.PublicClassifierNonFaithful realization.classifier :=
  classifierNonFaithful_of_kernelSeparation realization
    Helfer.CochainModel.closedTestInvariance kernelSeparation

theorem no_exact_representative_decoder :
    ¬ ∃ decoder : Set ℤ → Fin 2,
      Function.LeftInverse decoder realization.classifier.π :=
  noExactRepresentativeDecoder_of_kernelSeparation realization
    Helfer.CochainModel.closedTestInvariance kernelSeparation

/-- The common `(class, b)` observation of the two actual encrypted samples. -/
def observation : Observation (Set ℤ) Index ℝ :=
  (realization.classifier.π 0, observed)

def leftWitness : HiddenHodgeWitness realization observation where
  representative := 0
  class_eq := rfl

def rightWitness : HiddenHodgeWitness realization observation where
  representative := 1
  class_eq := same_public_class.symm

theorem left_target_eq_message :
    operativeTarget realization observation leftWitness = (sample 0).message.1 := by
  change (HCP.operativeHarmonicComponent (realization.laplacian 0) observed :
    Index → ℝ) = _
  exact congrArg WithLp.ofLp
    ((operativeHarmonicComponent_eq 0 observed).trans (sample_projection 0))

theorem right_target_eq_message :
    operativeTarget realization observation rightWitness = (sample 1).message.1 := by
  change (HCP.operativeHarmonicComponent (realization.laplacian 1) observed :
    Index → ℝ) = _
  exact congrArg WithLp.ofLp
    ((operativeHarmonicComponent_eq 1 observed).trans (sample_projection 1))

theorem same_observation_distinct_targets :
    operativeTarget realization observation leftWitness ≠
      operativeTarget realization observation rightWitness := by
  rw [left_target_eq_message, right_target_eq_message]
  intro h
  apply sample_messages_ne
  apply PiLp.ext
  intro i
  exact congrFun h i

theorem message_ne_zero (axis : Fin 2) : (sample axis).message.1 ≠ 0 := by
  intro h
  have hc := congrArg (fun b : C1 => b ⟨(), other axis⟩) h
  simp [sample, message] at hc

theorem both_targets_nonzero :
    operativeTarget realization observation leftWitness ≠ 0 ∧
      operativeTarget realization observation rightWitness ≠ 0 := by
  rw [left_target_eq_message, right_target_eq_message]
  constructor
  · intro h
    apply message_ne_zero 0
    apply PiLp.ext
    intro i
    exact congrFun h i
  · intro h
    apply message_ne_zero 1
    apply PiLp.ext
    intro i
    exact congrFun h i

/-- The common observation is shared by samples with the same exact component. -/
theorem sample_observation_and_exact_component :
    (sample 0).observed = (sample 1).observed ∧
      (sample 0).opening.exactComponent = (sample 1).opening.exactComponent := by
  simp only [sample_observed, sample_exactComponent, and_self]

theorem sample_public_observations_eq :
    (realization.classifier.π 0, ((sample 0).observed : Index → ℝ)) =
      (realization.classifier.π 1, ((sample 1).observed : Index → ℝ)) := by
  rw [same_public_class, sample_observed, sample_observed]

/-- One public input has two different nonzero, geometrically realized targets. -/
theorem shared_observation_distinct_nonzero_targets :
    ∃ (O : Observation (Set ℤ) Index ℝ)
      (w₀ w₁ : HiddenHodgeWitness realization O),
      operativeTarget realization O w₀ ≠ operativeTarget realization O w₁ ∧
        operativeTarget realization O w₀ ≠ 0 ∧
        operativeTarget realization O w₁ ≠ 0 :=
  ⟨observation, leftWitness, rightWitness,
    same_observation_distinct_targets, both_targets_nonzero⟩

/-- With its explicit harmonic lattice, each actual sample has precisely its
encoded message as the genuine discrete closest vector. -/
theorem cvp_solution_iff_message (axis : Fin 2) (v : CVP.AmbientVector Index) :
    CVP.Solution ((harmonicLatticePresentation axis).cvpInstance (sample axis)) v ↔
      v = (sample axis).message.1 := by
  simpa only [← sample_eq_encrypt_one axis, ← sample_message_eq_point axis] using
    (concreteSheafHCP_CVP_solution_iff_message (harmonicLatticePresentation axis)
      (fun _ : Fin 1 => 1) (opening axis) v)

theorem cvp_existsUnique (axis : Fin 2) :
    ∃! v, CVP.Solution
      ((harmonicLatticePresentation axis).cvpInstance (sample axis)) v := by
  simpa only [← sample_eq_encrypt_one axis] using
    (concreteSheafHCP_CVP_existsUnique (harmonicLatticePresentation axis)
      (fun _ : Fin 1 => 1) (opening axis))

/-- The left explicit-lattice CVP answer is the left operative target at the
same shared public input. -/
theorem cvp_solution_iff_left_operativeTarget (v : CVP.AmbientVector Index) :
    CVP.Solution ((harmonicLatticePresentation 0).cvpInstance (sample 0)) v ↔
      v = operativeTarget realization observation leftWitness := by
  rw [left_target_eq_message]
  exact cvp_solution_iff_message 0 v

/-- The right explicit-lattice instance selects the other operative target. -/
theorem cvp_solution_iff_right_operativeTarget (v : CVP.AmbientVector Index) :
    CVP.Solution ((harmonicLatticePresentation 1).cvpInstance (sample 1)) v ↔
      v = operativeTarget realization observation rightWitness := by
  rw [right_target_eq_message]
  exact cvp_solution_iff_message 1 v

theorem no_exact_public_solver {Aux : Type*}
    (solver : Solver Aux (Set ℤ) Index ℝ) (aux : Aux) :
    ¬ SolverExactOnOperativeTarget realization solver aux :=
  no_solver_exactOnOperativeTarget_of_kernelSeparation realization
    Helfer.CochainModel.closedTestInvariance kernelSeparation

theorem no_sound_and_harmonic_exact_public_solver {Aux : Type*}
    (solver : Solver Aux (Set ℤ) Index ℝ) (aux : Aux) :
    ¬ (SolverSoundOn realization solver aux ∧
      SolverExactOnHarmonic realization solver aux) := by
  rintro ⟨hsound, hexact⟩
  exact no_solver_on_kernelSeparation realization
    Helfer.CochainModel.closedTestInvariance kernelSeparation hsound hexact

/-- Any correct explicit-lattice CVP oracle remains auxiliary to this observation. -/
theorem cvp_oracle_insufficient
    (hOracle : ∃ O : CVP.Oracle Index Index, CVP.OracleCorrect O) :
    ¬ ∃ solver : Solver (CVP.Oracle Index Index) (Set ℤ) Index ℝ,
      ∀ O : CVP.Oracle Index Index, CVP.OracleCorrect O →
        SolverExactOnOperativeTarget realization solver O :=
  cvpOracle_insufficient_for_operativeTarget realization
    Helfer.CochainModel.closedTestInvariance kernelSeparation hOracle

/-! The following variant also separates the explicitly chosen integer
encodings. In the unweighted example both transported lattice coefficients
are one, even though the ambient harmonic vectors differ. -/

/-- Explicit integer coefficients: two on the left, one on the right. -/
def weightedCoefficients (axis : Fin 2) : Fin 1 → ℤ :=
  fun _ => if axis = 0 then 2 else 1

/-- The complementary coexact coordinate supplies one or two units of noise. -/
def weightedOpening (axis : Fin 2) : Sheaf.CellularSheaf.HodgeNoise (sheaf axis) where
  exactOpening := 0
  coexactOpening := EuclideanSpace.single ⟨(), 0⟩ (if axis = 0 then 1 else 2)

/-- These samples use the actual explicit integer lattice encoder. -/
def weightedSample (axis : Fin 2) :=
  (harmonicLatticePresentation axis).encrypt (weightedCoefficients axis)
    (weightedOpening axis)

def weightedObserved : C1 := unitCochain 0 + (2 : ℝ) • unitCochain 1

theorem weightedSample_message (axis : Fin 2) :
    (weightedSample axis).message.1 =
      (weightedCoefficients axis 0 : ℝ) • unitCochain (other axis) :=
  harmonicLatticePresentation_point axis (weightedCoefficients axis)

theorem weightedOpening_value (axis : Fin 2) :
    (weightedOpening axis).value =
      (if axis = 0 then (1 : ℝ) else 2) • unitCochain axis := by
  change (weightedOpening axis).exactComponent +
    (weightedOpening axis).coexactComponent = _
  have he : (weightedOpening axis).exactComponent = 0 := by
    simp [Sheaf.CellularSheaf.HodgeNoise.exactComponent, weightedOpening]
  rw [he, zero_add]
  change (sheaf axis).delta1.adjoint _ = _
  rw [delta1_adjoint_eq]
  apply PiLp.ext
  rintro ⟨⟨⟩, j⟩
  fin_cases axis <;> fin_cases j <;>
    norm_num [weightedOpening, unitCochain_apply, PiLp.single_apply]

theorem weightedSample_observed (axis : Fin 2) :
    (weightedSample axis).observed = weightedObserved := by
  change (weightedSample axis).message.1 + (weightedOpening axis).value = _
  rw [weightedSample_message, weightedOpening_value]
  fin_cases axis <;> simp [weightedCoefficients, weightedObserved, add_comm]

theorem weightedSample_exactComponent (axis : Fin 2) :
    (weightedSample axis).opening.exactComponent = 0 := by
  simp [weightedSample, Sheaf.CellularSheaf.HarmonicLatticePresentation.encrypt,
    Sheaf.CellularSheaf.HodgeNoise.exactComponent, weightedOpening]

theorem weighted_public_observations_eq :
    (realization.classifier.π 0, ((weightedSample 0).observed : Index → ℝ)) =
      (realization.classifier.π 1, ((weightedSample 1).observed : Index → ℝ)) := by
  rw [same_public_class, weightedSample_observed, weightedSample_observed]

theorem weighted_coefficients_values :
    weightedCoefficients 0 0 = 2 ∧ weightedCoefficients 1 0 = 1 := by decide

theorem weighted_coefficients_ne : weightedCoefficients 0 ≠ weightedCoefficients 1 := by
  intro h
  have hc := congrFun h 0
  norm_num [weightedCoefficients] at hc

theorem weightedSample_messages_ne :
    (weightedSample 0).message.1 ≠ (weightedSample 1).message.1 := by
  intro h
  have hc := congrArg (fun b : C1 => b ⟨(), 0⟩) h
  simp [weightedSample_message, weightedCoefficients] at hc

theorem weightedSample_message_ne_zero (axis : Fin 2) :
    (weightedSample axis).message.1 ≠ 0 := by
  intro h
  have hc := congrArg (fun b : C1 => b ⟨(), other axis⟩) h
  fin_cases axis <;> simp [weightedSample_message, weightedCoefficients] at hc

/-- The fixed shared raw input is `(1,2)` in the common ambient coordinates. -/
def weightedObservation : Observation (Set ℤ) Index ℝ :=
  (realization.classifier.π 0, weightedObserved)

def weightedWitness (axis : Fin 2) : HiddenHodgeWitness realization weightedObservation where
  representative := axis
  class_eq := theory_eq axis 0

theorem weighted_target_eq_message (axis : Fin 2) :
    operativeTarget realization weightedObservation (weightedWitness axis) =
      (weightedSample axis).message.1 := by
  change (HCP.operativeHarmonicComponent (realization.laplacian axis)
    weightedObserved : Index → ℝ) = _
  have hp : (sheaf axis).harmonicOneProjection weightedObserved =
      (weightedSample axis).message.1 := by
    rw [← weightedSample_observed axis]
    exact (weightedSample axis).harmonicOneProjection_observed
  exact congrArg WithLp.ofLp
    ((operativeHarmonicComponent_eq axis weightedObserved).trans hp)

theorem weighted_same_observation_distinct_targets :
    operativeTarget realization weightedObservation (weightedWitness 0) ≠
      operativeTarget realization weightedObservation (weightedWitness 1) := by
  rw [weighted_target_eq_message, weighted_target_eq_message]
  intro h
  apply weightedSample_messages_ne
  apply PiLp.ext
  intro i
  exact congrFun h i

theorem weighted_both_targets_nonzero :
    operativeTarget realization weightedObservation (weightedWitness 0) ≠ 0 ∧
      operativeTarget realization weightedObservation (weightedWitness 1) ≠ 0 := by
  rw [weighted_target_eq_message, weighted_target_eq_message]
  constructor
  · intro h
    apply weightedSample_message_ne_zero 0
    apply PiLp.ext
    intro i
    exact congrFun h i
  · intro h
    apply weightedSample_message_ne_zero 1
    apply PiLp.ext
    intro i
    exact congrFun h i

theorem weighted_cvp_solution_iff_operativeTarget
    (axis : Fin 2) (v : CVP.AmbientVector Index) :
    CVP.Solution
        ((harmonicLatticePresentation axis).cvpInstance (weightedSample axis)) v ↔
      v = operativeTarget realization weightedObservation (weightedWitness axis) := by
  rw [weighted_target_eq_message]
  exact concreteSheafHCP_CVP_solution_iff_message (harmonicLatticePresentation axis)
    (weightedCoefficients axis) (weightedOpening axis) v

theorem weighted_cvp_existsUnique (axis : Fin 2) :
    ∃! v, CVP.Solution
      ((harmonicLatticePresentation axis).cvpInstance (weightedSample axis)) v :=
  concreteSheafHCP_CVP_existsUnique (harmonicLatticePresentation axis)
    (weightedCoefficients axis) (weightedOpening axis)

/-- The chosen integer encodings differ at the identical `(class,b)` input.
This is finite exact-recovery failure, without a distributional security claim. -/
theorem no_exact_encoded_message_decoder :
    ¬ ∃ decoder : Observation (Set ℤ) Index ℝ → ℤ,
      ∀ axis : Fin 2,
        decoder (realization.classifier.π axis, (weightedSample axis).observed) =
          weightedCoefficients axis 0 := by
  rintro ⟨decoder, hdecoder⟩
  have h0 := hdecoder 0
  have h1 := hdecoder 1
  rw [weightedSample_observed] at h0 h1
  rw [← same_public_class] at h1
  have h : (2 : ℤ) = 1 := by
    calc
      2 = decoder (realization.classifier.π 0, weightedObserved) := by
        simpa [weightedCoefficients] using h0.symm
      _ = 1 := by simpa [weightedCoefficients] using h1
  norm_num at h

end Hcrypt.HCP.AxisFamily
