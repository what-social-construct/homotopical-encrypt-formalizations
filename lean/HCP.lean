module

/-
Core formalization of the Harmonic Cochain Problem (HCP).

This module owns HCP definitions, ambiguity predicates, the typed Helfer
realization, and public solver contracts. CVP comparison and impossibility
theorems remain in `Hardness.lean`.
-/

public import Mathlib.Tactic
public import Laplacian.Hodge
public import Axioms.HelferFOL

@[expose] public section

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

def Hodge_Instance (N : Type) [Fintype N] (R : Type) [CommRing R] :=
  Matrix N N R × (N → R)

/--
Matrix-level harmonicity for an abstract hidden operator.

This is the generic predicate used by hidden-operator hardness theorems. The
structured projection-model predicate is `HomotopicalEncryption.Laplacian.IsHarmonic`; the two
are connected below by `matrix_harmonic_iff_projection_isHarmonic` when
`Δ = Δ_W`.
-/
def MatrixIsHarmonic {N : Type} [Fintype N] {R : Type} [CommRing R]
  (Δ : Matrix N N R) (h : N → R) : Prop :=
  Matrix.mulVec Δ h = 0

/--
A public projection from hidden Hodge operators to observable public data.

This is deliberately lossy in the intended security model: public data may
identify a class of compatible hidden operators rather than one canonical
operator. Concrete public artifacts such as cochain commitments, hashes, or
class fingerprints are represented here only through this abstract public
projection.
-/
def PublicProjection (N : Type) [Fintype N] (R : Type) [CommRing R] (P : Type) :=
  Matrix N N R → P

/-- Two hidden operators are publicly equivalent under the projection. -/
def PubliclyEquivalent
  {N : Type} [Fintype N] {R : Type} [CommRing R] {P : Type}
  (pub : PublicProjection N R P) (Δ₁ Δ₂ : Matrix N N R) : Prop :=
  pub Δ₁ = pub Δ₂

/-- The public fiber over an observable value. -/
def HiddenOperatorFiber
  {N : Type} [Fintype N] {R : Type} [CommRing R] {P : Type}
  (pub : PublicProjection N R P) (p : P) : Set (Matrix N N R) :=
  {Δ | pub Δ = p}

/-- The class of hidden operators compatible with the public value of `Δ`. -/
def HiddenOperatorClass
  {N : Type} [Fintype N] {R : Type} [CommRing R] {P : Type}
  (pub : PublicProjection N R P) (Δ : Matrix N N R) : Set (Matrix N N R) :=
  HiddenOperatorFiber pub (pub Δ)

/-- A public projection is lossy when distinct hidden operators share public data. -/
def LossyPublicProjection
  {N : Type} [Fintype N] {R : Type} [CommRing R] {P : Type}
  (pub : PublicProjection N R P) : Prop :=
  ∃ Δ₁ Δ₂ : Matrix N N R, Δ₁ ≠ Δ₂ ∧ PubliclyEquivalent pub Δ₁ Δ₂

/-- Two operators have the same harmonic kernel when they agree on harmonicity. -/
def SameKernel
  {N : Type} [Fintype N] {R : Type} [CommRing R]
  (Δ₁ Δ₂ : Matrix N N R) : Prop :=
  ∀ v : N → R, MatrixIsHarmonic Δ₁ v ↔ MatrixIsHarmonic Δ₂ v

/--
Kernel ambiguity strengthens public lossiness: publicly equivalent hidden
operators may nevertheless determine different Hodge kernels.
-/
def KernelAmbiguous
  {N : Type} [Fintype N] {R : Type} [CommRing R] {P : Type}
  (pub : PublicProjection N R P) : Prop :=
  ∃ Δ₁ Δ₂ : Matrix N N R, PubliclyEquivalent pub Δ₁ Δ₂ ∧ ¬ SameKernel Δ₁ Δ₂

/--
Public-compatible Hodge ambiguity.

This is the exact hidden-operator obstruction used in the security argument:
the same public class contains two hidden operators that disagree on whether the
same public cochain is harmonic.
-/
def PublicCompatibleHodgeAmbiguity
  {N : Type} [Fintype N] {R : Type} [CommRing R] {P : Type}
  (pub : PublicProjection N R P) : Prop :=
  ∃ (Δ₁ Δ₂ : Matrix N N R) (b : N → R),
    PubliclyEquivalent pub Δ₁ Δ₂ ∧
    (∃ h₁, MatrixIsHarmonic Δ₁ h₁ ∧ h₁ = b) ∧
    (¬ ∃ h₂, MatrixIsHarmonic Δ₂ h₂ ∧ h₂ = b)

/-- Every hidden operator lies in its own public class. -/
theorem mem_hiddenOperatorClass_self
  {N : Type} [Fintype N] {R : Type} [CommRing R] {P : Type}
  (pub : PublicProjection N R P) (Δ : Matrix N N R) :
  Δ ∈ HiddenOperatorClass pub Δ := by
  rfl

/-- Same-kernel equivalence is reflexive. -/
theorem sameKernel_refl
  {N : Type} [Fintype N] {R : Type} [CommRing R]
  (Δ : Matrix N N R) :
  SameKernel Δ Δ := by
  intro v
  rfl

/-- Kernel ambiguity implies the public projection is genuinely lossy. -/
theorem kernelAmbiguous_implies_lossy
  {N : Type} [Fintype N] {R : Type} [CommRing R] {P : Type}
  {pub : PublicProjection N R P} :
  KernelAmbiguous pub → LossyPublicProjection pub := by
  intro h
  rcases h with ⟨Δ₁, Δ₂, hpub, hnot⟩
  refine ⟨Δ₁, Δ₂, ?_, hpub⟩
  intro h_eq
  apply hnot
  cases h_eq
  exact sameKernel_refl Δ₁

/--
A public-compatible Hodge ambiguity gives genuine kernel ambiguity.

This is the bridge from "the same public data is compatible with multiple
hidden geometries" to "there is no single explicit lattice/kernel for CVP to
act on."
-/
theorem kernelAmbiguous_of_publicCompatibleHodgeAmbiguity
  {N : Type} [Fintype N] {R : Type} [CommRing R] {P : Type}
  {pub : PublicProjection N R P} :
  PublicCompatibleHodgeAmbiguity pub → KernelAmbiguous pub := by
  intro h
  rcases h with ⟨Δ₁, Δ₂, b, hpub, hb₁, hb₂⟩
  refine ⟨Δ₁, Δ₂, hpub, ?_⟩
  intro hsame
  rcases hb₁ with ⟨h₁, hh₁_harm, hh₁_eq⟩
  have hb_harm₁ : MatrixIsHarmonic Δ₁ b := by
    simpa [hh₁_eq] using hh₁_harm
  have hb_harm₂ : MatrixIsHarmonic Δ₂ b := (hsame b).1 hb_harm₁
  exact hb₂ ⟨b, hb_harm₂, rfl⟩

-- ════════════════════════════════════════════════════════════════════
-- Typed Helfer semantics / HCP hidden-operator bridge
-- ═════════════════════════════════════════════════════════════════════

namespace HomotopicalEncryption.HCPBridge

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u₁ u₂ v₁ v₂ w uRep uAux

/--
An HCP realization extends a homotopy-invariant Helfer interpretation by
presentation-level Hodge data.

The semantic interpretation and the hidden Laplacian are separate on purpose.
If the Laplacian and its harmonicity predicate belonged to the invariant
first-order signature, closed-formula invariance would obstruct, rather than
imply, the kernel-separation witness below.
-/
structure Realization
    (C : Type u₂) [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    (S : Helfer.Signature.{u₁, v₁})
    (sem : Helfer.ClosedSemantics (C := C) S)
    (Rep : Type uRep) (N : Type) [Fintype N]
    (R : Type) [CommRing R] (P : Type) where
  /-- Homotopy-invariant semantic core of a hidden representative. -/
  interpretation : Rep → Helfer.Interpretation C S
  /-- Operative degree-one Hodge operator attached to the representative. -/
  laplacian : Rep → Matrix N N R
  /-- Public classifier on hidden representatives. -/
  classifier : Axioms.PublicClassifier Rep P
  /-- Matrix-level public projection used by the existing hardness lemmas. -/
  publicProjection : _root_.PublicProjection N R P
  /-- Public classification of a closed first-order theory. -/
  classifyTheory : Set sem.ClosedFormula → P
  /-- The representative classifier factors through its invariant theory. -/
  classifier_factors : ∀ r,
    classifier.π r = classifyTheory (Helfer.ClosedTheory sem (interpretation r))
  /-- The matrix projection agrees with the representative classifier on realized operators. -/
  operator_classifier_factors : ∀ r,
    publicProjection (laplacian r) = classifier.π r

variable
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N]
    {R : Type} [CommRing R] {P : Type}

/--
Optional reflection requirement for a realization whose public classes are
exactly its declared semantic homotopy classes, once closed-test invariance
supplies the forward implication.

This concerns the semantic interpretations. Distinct equivalent representatives
and different operative kernels can share a class; an equivalence transport is
not made part of the public observation.
-/
def ReflectsHomotopyEquivalence
    (X : Realization C S sem Rep N R P) : Prop :=
  ∀ {r s : Rep}, Axioms.SamePublicClass X.classifier r s →
    Helfer.HomotopyEquivalent (X.interpretation r) (X.interpretation s)

/-- Homotopy equivalence of semantic cores gives equality of the factored classifier. -/
theorem samePublicClass_of_homotopyEquivalent
    (X : Realization C S sem Rep N R P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    {r s : Rep}
    (hrs : Helfer.HomotopyEquivalent (X.interpretation r) (X.interpretation s)) :
    Axioms.SamePublicClass X.classifier r s := by
  calc
    X.classifier.π r =
        X.classifyTheory (Helfer.ClosedTheory sem (X.interpretation r)) :=
      X.classifier_factors r
    _ = X.classifyTheory (Helfer.ClosedTheory sem (X.interpretation s)) := by
      rw [Helfer.closedTheory_eq sem hInv hrs]
    _ = X.classifier.π s := (X.classifier_factors s).symm

/-- Closed-test invariance and optional reflection make public class equality exact. -/
theorem samePublicClass_iff_homotopyEquivalent
    (X : Realization C S sem Rep N R P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    (hReflect : ReflectsHomotopyEquivalence X)
    {r s : Rep} :
    Axioms.SamePublicClass X.classifier r s ↔
      Helfer.HomotopyEquivalent (X.interpretation r) (X.interpretation s) := by
  constructor
  · intro hclass
    exact hReflect hclass
  · intro hequiv
    exact samePublicClass_of_homotopyEquivalent X hInv hequiv

/-- The existing public class is the semantic homotopy class under optional reflection. -/
theorem publicClassOf_eq_setOf_homotopyEquivalent
    (X : Realization C S sem Rep N R P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    (hReflect : ReflectsHomotopyEquivalence X)
    (r : Rep) :
    Axioms.PublicClassOf X.classifier r =
      {s | Helfer.HomotopyEquivalent (X.interpretation s) (X.interpretation r)} := by
  ext s
  change Axioms.SamePublicClass X.classifier s r ↔ _
  exact samePublicClass_iff_homotopyEquivalent X hInv hReflect

/-- The representative and matrix classifiers agree on realized hidden operators. -/
theorem publiclyEquivalent_laplacians_of_homotopyEquivalent
    (X : Realization C S sem Rep N R P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    {r s : Rep}
    (hrs : Helfer.HomotopyEquivalent (X.interpretation r) (X.interpretation s)) :
    _root_.PubliclyEquivalent X.publicProjection (X.laplacian r) (X.laplacian s) := by
  calc
    X.publicProjection (X.laplacian r) = X.classifier.π r :=
      X.operator_classifier_factors r
    _ = X.classifier.π s :=
      samePublicClass_of_homotopyEquivalent X hInv hrs
    _ = X.publicProjection (X.laplacian s) :=
      (X.operator_classifier_factors s).symm

/--
An independent witness that the presentation-level Hodge extensions of two
homotopy-equivalent semantic cores disagree on one cochain. The last two
fields are extra HCP data; kernel disagreement is not inferred from semantic
equivalence.
-/
structure KernelSeparationWitness
    (X : Realization C S sem Rep N R P) where
  left : Rep
  right : Rep
  input : N → R
  semanticEquivalence :
    Helfer.HomotopyEquivalent (X.interpretation left) (X.interpretation right)
  harmonic_left : _root_.MatrixIsHarmonic (X.laplacian left) input
  not_harmonic_right : ¬ _root_.MatrixIsHarmonic (X.laplacian right) input

/-- The typed semantic bridge plus Hodge separation yields public-compatible ambiguity. -/
theorem publicCompatibleHodgeAmbiguity_of_kernelSeparation
    (X : Realization C S sem Rep N R P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    (witness : KernelSeparationWitness X) :
    _root_.PublicCompatibleHodgeAmbiguity X.publicProjection := by
  refine ⟨X.laplacian witness.left, X.laplacian witness.right, witness.input,
    publiclyEquivalent_laplacians_of_homotopyEquivalent X hInv
      witness.semanticEquivalence, ?_, ?_⟩
  · exact ⟨witness.input, witness.harmonic_left, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact witness.not_harmonic_right hh

/-- The typed bridge packages the existing kernel-ambiguity implication. -/
theorem kernelAmbiguous_of_kernelSeparation
    (X : Realization C S sem Rep N R P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    (witness : KernelSeparationWitness X) :
    _root_.KernelAmbiguous X.publicProjection :=
  _root_.kernelAmbiguous_of_publicCompatibleHodgeAmbiguity
    (publicCompatibleHodgeAmbiguity_of_kernelSeparation X hInv witness)

/-- Kernel separation also makes the matrix-level public projection lossy. -/
theorem lossyPublicProjection_of_kernelSeparation
    (X : Realization C S sem Rep N R P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    (witness : KernelSeparationWitness X) :
    _root_.LossyPublicProjection X.publicProjection :=
  _root_.kernelAmbiguous_implies_lossy
    (kernelAmbiguous_of_kernelSeparation X hInv witness)

/-- The actual public input seen by a representative-indexed HCP solver. -/
abbrev Observation (P N R : Type*) := P × (N → R)

/-- A solver receives auxiliary information and the public class/cochain pair. -/
abbrev Solver (Aux : Type uAux) (P N R : Type) :=
  Aux → Observation P N R → (N → R)

/-- Soundness only for hidden representatives admitted by this realization. -/
def SolverSoundOn
    (X : Realization C S sem Rep N R P)
    {Aux : Type uAux} (solver : Solver Aux P N R) (aux : Aux) : Prop :=
  ∀ (r : Rep) (b : N → R),
    _root_.MatrixIsHarmonic (X.laplacian r)
      (solver aux (X.classifier.π r, b))

/-- Exactness on already-harmonic inputs for admitted representatives. -/
def SolverExactOnHarmonic
    (X : Realization C S sem Rep N R P)
    {Aux : Type uAux} (solver : Solver Aux P N R) (aux : Aux) : Prop :=
  ∀ (r : Rep) (b : N → R),
    _root_.MatrixIsHarmonic (X.laplacian r) b →
      solver aux (X.classifier.π r, b) = b

end HomotopicalEncryption.HCPBridge

-- ═══════════════════════════════════════════════════════════════════════
-- Hodge encryption/decryption and the operative HCP recovery target
-- ═══════════════════════════════════════════════════════════════════════

namespace HomotopicalEncryption.HCP

open scoped RealInnerProductSpace

/-- The finite Euclidean cochain carrier used by the matrix-level HCP model. -/
abbrev CochainSpace (N : Type) [Fintype N] := EuclideanSpace ℝ N

/--
The orthogonal Hodge-coordinate equivalence

`W × Wᗮ ≃ C¹`, `(h,e) ↦ h + e`.

This is the precise bijection behind Hodge encryption.  The encryption
randomness/noise is part of the source; randomized encryption is not asserted
to be a bijection from harmonic plaintexts alone.
-/
noncomputable def hodgeDecompositionEquiv
    {N : Type} [Fintype N]
    (W : Submodule ℝ (CochainSpace N)) [W.HasOrthogonalProjection] :
    (W × W.orthogonal) ≃ₗ[ℝ] CochainSpace N :=
  W.prodEquivOfIsCompl W.orthogonal
    W.isCompl_orthogonal

/-- Encrypt a harmonic plaintext by adding an orthogonal Hodge-noise component. -/
noncomputable def encrypt
    {N : Type} [Fintype N]
    (W : Submodule ℝ (CochainSpace N)) [W.HasOrthogonalProjection]
    (h : W) (e : W.orthogonal) : CochainSpace N :=
  hodgeDecompositionEquiv W (h, e)

/-- Recover both Hodge coordinates of a cochain. -/
noncomputable def split
    {N : Type} [Fintype N]
    (W : Submodule ℝ (CochainSpace N)) [W.HasOrthogonalProjection]
    (b : CochainSpace N) : W × W.orthogonal :=
  (hodgeDecompositionEquiv W).symm b

/-- Decrypt by retaining the harmonic coordinate. -/
noncomputable def decrypt
    {N : Type} [Fintype N]
    (W : Submodule ℝ (CochainSpace N)) [W.HasOrthogonalProjection]
    (b : CochainSpace N) : W :=
  (split W b).1

/-- The noise coordinate recovered by the full inverse Hodge splitting. -/
noncomputable def noiseComponent
    {N : Type} [Fintype N]
    (W : Submodule ℝ (CochainSpace N)) [W.HasOrthogonalProjection]
    (b : CochainSpace N) : W.orthogonal :=
  (split W b).2

@[simp] theorem split_encrypt
    {N : Type} [Fintype N]
    (W : Submodule ℝ (CochainSpace N)) [W.HasOrthogonalProjection]
    (h : W) (e : W.orthogonal) :
    split W (encrypt W h e) = (h, e) :=
  (hodgeDecompositionEquiv W).symm_apply_apply (h, e)

@[simp] theorem encrypt_split
    {N : Type} [Fintype N]
    (W : Submodule ℝ (CochainSpace N)) [W.HasOrthogonalProjection]
    (b : CochainSpace N) :
    encrypt W (decrypt W b) (noiseComponent W b) = b :=
  (hodgeDecompositionEquiv W).apply_symm_apply b

/-- Hodge decryption exactly recovers every harmonic plaintext. -/
@[simp] theorem decrypt_encrypt
    {N : Type} [Fintype N]
    (W : Submodule ℝ (CochainSpace N)) [W.HasOrthogonalProjection]
    (h : W) (e : W.orthogonal) :
    decrypt W (encrypt W h e) = h :=
  congrArg Prod.fst (split_encrypt W h e)

theorem decrypt_eq_orthogonalProjection
    {N : Type} [Fintype N]
    (W : Submodule ℝ (CochainSpace N)) [W.HasOrthogonalProjection]
    (b : CochainSpace N) :
    decrypt W b = W.orthogonalProjectionOnto b := by
  change
    W.projectionOnto W.orthogonal W.isCompl_orthogonal b =
      W.orthogonalProjectionOnto b
  exact (W.orthogonalProjectionOnto_apply_eq_projectionOnto b).symm

/-- The HCP decryption map is the existing harmonic projection. -/
theorem decrypt_coe_eq_harmonicProjection
    {N : Type} [Fintype N]
    (W : Submodule ℝ (CochainSpace N)) [W.HasOrthogonalProjection]
    (b : CochainSpace N) :
    (decrypt W b : CochainSpace N) =
      Laplacian.harmonicProjection W b := by
  rw [decrypt_eq_orthogonalProjection]
  rfl

/-- Harmonic kernel of a matrix-presented hidden operator. -/
def matrixHarmonicSubspace
    {N : Type} [Fintype N]
    (Δ : Matrix N N ℝ) : Submodule ℝ (CochainSpace N) :=
  LinearMap.ker ((Matrix.mulVecLin Δ).comp
    (WithLp.linearEquiv 2 ℝ (N → ℝ)).toLinearMap)

/--
The unique operative HCP target: the harmonic component of `b` for the
selected hidden operator, rather than an arbitrary element of its kernel.
-/
noncomputable def operativeHarmonicComponent
    {N : Type} [Fintype N]
    (Δ : Matrix N N ℝ) (b : CochainSpace N) : CochainSpace N :=
  (matrixHarmonicSubspace Δ).starProjection b

theorem operativeHarmonicComponent_is_harmonic
    {N : Type} [Fintype N]
    (Δ : Matrix N N ℝ) (b : CochainSpace N) :
    _root_.MatrixIsHarmonic Δ (operativeHarmonicComponent Δ b) := by
  change operativeHarmonicComponent Δ b ∈ matrixHarmonicSubspace Δ
  exact (matrixHarmonicSubspace Δ).starProjection_apply_mem b

theorem operativeHarmonicComponent_eq_self_of_harmonic
    {N : Type} [Fintype N]
    (Δ : Matrix N N ℝ) (b : CochainSpace N)
    (hb : _root_.MatrixIsHarmonic Δ b) :
    operativeHarmonicComponent Δ b = b := by
  apply (matrixHarmonicSubspace Δ).starProjection_eq_self_iff.mpr
  exact hb

/-- Orthogonal projection onto the operative harmonic kernel is idempotent. -/
@[simp] theorem operativeHarmonicComponent_idempotent
    {N : Type} [Fintype N]
    (Δ : Matrix N N ℝ) (b : CochainSpace N) :
    operativeHarmonicComponent Δ (operativeHarmonicComponent Δ b) =
      operativeHarmonicComponent Δ b :=
  operativeHarmonicComponent_eq_self_of_harmonic Δ _
    (operativeHarmonicComponent_is_harmonic Δ b)

end HomotopicalEncryption.HCP

namespace HomotopicalEncryption.HCPBridge

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u₁ u₂ v₁ v₂ uRep uAux

/--
A private witness binds a public observation to its operative hidden
representative.  The representative is not part of the public observation.
-/
structure HiddenHodgeWitness
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N] {P : Type}
    (X : Realization C S sem Rep N ℝ P)
    (observation : Observation P N ℝ) where
  representative : Rep
  class_eq : X.classifier.π representative = observation.1

/-- The unique harmonic component selected by a bound hidden witness. -/
noncomputable def operativeTarget
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N] {P : Type}
    (X : Realization C S sem Rep N ℝ P)
    (observation : Observation P N ℝ)
    (witness : HiddenHodgeWitness X observation) : N → ℝ :=
  HCP.operativeHarmonicComponent
    (X.laplacian witness.representative) (WithLp.toLp 2 observation.2)

/-- A proposed answer solves the particular operative witnessed HCP instance. -/
def IsOperativeSolution
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N] {P : Type}
    (X : Realization C S sem Rep N ℝ P)
    (observation : Observation P N ℝ)
    (witness : HiddenHodgeWitness X observation)
    (output : N → ℝ) : Prop :=
  output = operativeTarget X observation witness

/--
A public solver is exact on the operative HCP target when it returns the
projection selected by every hidden witness compatible with its observation.
This is the direct recovery contract; it is stronger than merely returning
some harmonic vector.
-/
def SolverExactOnOperativeTarget
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N] {P : Type}
    (X : Realization C S sem Rep N ℝ P)
    {Aux : Type uAux} (solver : Solver Aux P N ℝ) (aux : Aux) : Prop :=
  ∀ (observation : Observation P N ℝ)
    (witness : HiddenHodgeWitness X observation),
    IsOperativeSolution X observation witness (solver aux observation)

theorem operativeTarget_is_harmonic
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N] {P : Type}
    (X : Realization C S sem Rep N ℝ P)
    (observation : Observation P N ℝ)
    (witness : HiddenHodgeWitness X observation) :
    _root_.MatrixIsHarmonic (X.laplacian witness.representative)
      (operativeTarget X observation witness) :=
  HCP.operativeHarmonicComponent_is_harmonic _ _

/--
An isometric reparameterization of two HCP presentations.  The private
transport and its inverse are bijective; the public classifier is not asserted
to be invertible.
-/
structure IsometricPresentationEquivalence
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N] {P : Type}
    (X : Realization C S sem Rep N ℝ P) (left right : Rep) where
  semanticEquivalence :
    Helfer.HomotopyEquivalent
      (X.interpretation left) (X.interpretation right)
  transport : HCP.CochainSpace N ≃ₗᵢ[ℝ] HCP.CochainSpace N
  laplacian_naturality : ∀ b,
    Matrix.mulVec (X.laplacian right) (transport b) =
      transport (WithLp.toLp 2 (Matrix.mulVec (X.laplacian left) b))

namespace IsometricPresentationEquivalence

theorem harmonic_iff_transport
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N] {P : Type}
    {X : Realization C S sem Rep N ℝ P} {left right : Rep}
    (T : IsometricPresentationEquivalence X left right)
    (b : N → ℝ) :
    _root_.MatrixIsHarmonic (X.laplacian left) b ↔
      _root_.MatrixIsHarmonic (X.laplacian right) (T.transport (WithLp.toLp 2 b)) := by
  constructor
  · intro hb
    rw [_root_.MatrixIsHarmonic, T.laplacian_naturality, hb]
    simp
  · intro hb
    rw [_root_.MatrixIsHarmonic] at hb ⊢
    have htransport :
        T.transport (WithLp.toLp 2 (Matrix.mulVec (X.laplacian left) b)) = 0 := by
      apply WithLp.ofLp_injective
      rw [← T.laplacian_naturality]
      exact hb
    have hz : WithLp.toLp 2 (Matrix.mulVec (X.laplacian left) b) = 0 :=
      T.transport.injective (by simpa using htransport)
    simpa using congrArg WithLp.ofLp hz

/-- Isometric Laplacian transport maps the source harmonic kernel onto the target one. -/
theorem map_matrixHarmonicSubspace
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N] {P : Type}
    {X : Realization C S sem Rep N ℝ P} {left right : Rep}
    (T : IsometricPresentationEquivalence X left right) :
    Submodule.map T.transport.toLinearEquiv.toLinearMap
        (HCP.matrixHarmonicSubspace (X.laplacian left)) =
      HCP.matrixHarmonicSubspace (X.laplacian right) := by
  ext y
  rw [Submodule.mem_map_equiv
    (HCP.matrixHarmonicSubspace (X.laplacian left))]
  change
    _root_.MatrixIsHarmonic (X.laplacian left) (T.transport.symm y) ↔
      _root_.MatrixIsHarmonic (X.laplacian right) y
  simpa using T.harmonic_iff_transport (T.transport.symm y)

/--
The operative HCP projection is natural when the cochain and its hidden
presentation are transported together.
-/
theorem operativeHarmonicComponent_naturality
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N] {P : Type}
    {X : Realization C S sem Rep N ℝ P} {left right : Rep}
    (T : IsometricPresentationEquivalence X left right)
    (b : HCP.CochainSpace N) :
    T.transport
        (HCP.operativeHarmonicComponent (X.laplacian left) b) =
      HCP.operativeHarmonicComponent
        (X.laplacian right) (T.transport b) := by
  change
    T.transport
        ((HCP.matrixHarmonicSubspace (X.laplacian left)).starProjection b) =
      (HCP.matrixHarmonicSubspace (X.laplacian right)).starProjection
        (T.transport b)
  rw [← T.map_matrixHarmonicSubspace]
  simpa using
    (Submodule.starProjection_map_apply T.transport
      (HCP.matrixHarmonicSubspace (X.laplacian left)) (T.transport b)).symm

end IsometricPresentationEquivalence

/--
The same raw public coordinate is harmonic on the left, but its private
transport-preimage is not.  By Laplacian naturality this is exactly the
non-stabilization condition needed for right-side non-harmonicity.
-/
structure FixedCoordinateNonstabilization
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N] {P : Type}
    {X : Realization C S sem Rep N ℝ P} {left right : Rep}
    (T : IsometricPresentationEquivalence X left right) where
  input : N → ℝ
  harmonic_left :
    _root_.MatrixIsHarmonic (X.laplacian left) input
  preimage_not_harmonic_left :
    ¬ _root_.MatrixIsHarmonic (X.laplacian left)
      (T.transport.symm (WithLp.toLp 2 input))

/-- Chain-isometric transport plus fixed-coordinate non-stabilization constructs HCP separation. -/
def kernelSeparationWitness_of_isometricNonstabilization
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N] {P : Type}
    {X : Realization C S sem Rep N ℝ P} {left right : Rep}
    (T : IsometricPresentationEquivalence X left right)
    (hfixed : FixedCoordinateNonstabilization T) :
    KernelSeparationWitness X where
  left := left
  right := right
  input := hfixed.input
  semanticEquivalence := T.semanticEquivalence
  harmonic_left := hfixed.harmonic_left
  not_harmonic_right := by
    intro hright
    apply hfixed.preimage_not_harmonic_left
    apply (T.harmonic_iff_transport
      (T.transport.symm (WithLp.toLp 2 hfixed.input))).2
    simpa using hright

theorem kernelSeparation_left_ne_right
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N]
    {P : Type} {X : Realization C S sem Rep N ℝ P}
    (witness : KernelSeparationWitness X) :
    witness.left ≠ witness.right := by
  intro h
  apply witness.not_harmonic_right
  simpa [h] using witness.harmonic_left

/-- Kernel separation makes the representative classifier non-faithful. -/
theorem classifierNonFaithful_of_kernelSeparation
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N]
    {P : Type} (X : Realization C S sem Rep N ℝ P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    (witness : KernelSeparationWitness X) :
    Axioms.PublicClassifierNonFaithful X.classifier :=
  ⟨witness.left, witness.right,
    kernelSeparation_left_ne_right witness,
    samePublicClass_of_homotopyEquivalent X hInv
      witness.semanticEquivalence⟩

/--
The public classifier has no exact decoder recovering every hidden
representative.  This is an information-theoretic non-reconstruction result,
not an IND-style computational privacy theorem.
-/
theorem noExactRepresentativeDecoder_of_kernelSeparation
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N]
    {P : Type} (X : Realization C S sem Rep N ℝ P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    (witness : KernelSeparationWitness X) :
    ¬ ∃ decoder : P → Rep, Function.LeftInverse decoder X.classifier.π := by
  rintro ⟨decoder, hdecoder⟩
  apply kernelSeparation_left_ne_right witness
  calc
    witness.left = decoder (X.classifier.π witness.left) :=
      (hdecoder witness.left).symm
    _ = decoder (X.classifier.π witness.right) := by
      rw [samePublicClass_of_homotopyEquivalent X hInv
        witness.semanticEquivalence]
    _ = witness.right := hdecoder witness.right

end HomotopicalEncryption.HCPBridge
