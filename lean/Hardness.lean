module

/-
Formal verification of the HCP impossibility and CVP-comparison layer.

Paper correspondence:
- Paper 1 Sections 2--3: hidden-kernel ambiguity, linear-image comparison and
  the discrete-CVP oracle-insufficiency corollaries. Core definitions live in
  HCP.lean.
- Paper 1's selected statement crosswalk records the corresponding Hodge/CVP
  groups and their explicit hypotheses.

Terminology:
- `CVP` := the discrete closest-vector problem from `CVP.lean`, with integer
  coefficient vectors in a real ambient space.
- `presented linear image` := the field-linear subspace `B R^n`; this is not a
  lattice and is used only for the kernel/image linear algebra below.
- `HCP hidden-operator hardness` := recovery of the harmonic cochain from
  public homotopy-class and cochain/commitment-facing observations when the
  operative Laplacian and its harmonic kernel are hidden.
- `hidden-operator model` := the attacker sees only public data, while the
  actual fibration representative, Laplacian `Δ`, and harmonic kernel
  `ker(Δ)` remain hidden up to the public equivalence relation.

This module verifies the formal comparison used by the paper:
1. **Hodge Decomposition**: Constructs mutually orthogonal harmonic, exact,
   and coexact parts (`Hodge_Decomposition_Theorem`) and proves their
   uniqueness (`Hodge_Decomposition_unique`).
2. **Presented linear-image comparison**: Proves that any finite-dimensional
   field-linear image can be realized as a matrix kernel
   (`Hodge_GeneratedSubspace_Reduction_Proof`).
3. **Discrete harmonic-lattice bridge**: Given an explicit lattice
   `Λ ⊆ W = ker(Δ_W)`, proves the Pythagorean distance decomposition and that
   projecting the target onto `W` preserves the closest lattice vectors
   (`HarmonicCVPBridge.solution_iff_projectedTarget`).
4. **Typed Helfer/HCP consequence**: Consumes the realization, classifier, and
   kernel-separation interfaces from `HCP.lean`. A separation witness yields
   incompatible operative targets and rules out a public solver, even with a
   correct explicit-CVP oracle as auxiliary data. The obstruction persists
   in every compatible family containing the same separated pair.

The formal proofs separate the presented-subspace projection problem, the
discrete known-lattice CVP problem, and the hidden-operator recovery problem.

Important scope note:
- the kernel/image theorems are linear algebra and do not constitute a
  reduction from discrete CVP;
- the explicit HCP/CVP bridge starts only after a discrete lattice `Λ` inside
  the harmonic subspace has been supplied; it does not identify the whole real
  kernel with that lattice;
- the typed oracle-insufficiency theorem is conditional on an explicit HCP
  realization and a `KernelSeparationWitness`; equivalence alone does not
  imply kernel disagreement;
- the theorem is an information-theoretic no-uniform-solver statement for the
  stated deterministic interface, not by itself an asymptotic complexity
  lower bound;
- accordingly, the attacker is not given a canonically presented kernel, but must
  first identify which hidden representative determines the operative subspace
  `ker(Δ)`;
- a discrete-CVP oracle may be granted as an auxiliary oracle, but it cannot
  resolve two hidden operators that are compatible with the same public input;
-/

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import CVP
public import HCP
public import Sheaf.HarmonicLattice

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

namespace HomotopicalEncryption.HCPBridge

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u₁ u₂ v₁ v₂ w uRep uAux

variable
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Helfer.Signature.{u₁, v₁}}
    {sem : Helfer.ClosedSemantics (C := C) S}
    {Rep : Type uRep} {N : Type} [Fintype N]
    {R : Type} [CommRing R] {P : Type}

/-- One ambiguous public observation rules out simultaneous soundness and exactness. -/
theorem no_solver_on_kernelSeparation
    (X : Realization C S sem Rep N R P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    (witness : KernelSeparationWitness X)
    {Aux : Type uAux} {solver : Solver Aux P N R} {aux : Aux}
    (hsound : SolverSoundOn X solver aux)
    (hexact : SolverExactOnHarmonic X solver aux) : False := by
  have hclass : X.classifier.π witness.left = X.classifier.π witness.right :=
    samePublicClass_of_homotopyEquivalent X hInv witness.semanticEquivalence
  have hout : solver aux (X.classifier.π witness.left, witness.input) = witness.input :=
    hexact witness.left witness.input witness.harmonic_left
  have hright := hsound witness.right witness.input
  rw [← hclass] at hright
  rw [hout] at hright
  exact witness.not_harmonic_right hright

/--
A kernel-separation witness selects two different operative HCP targets for
one and the same public observation.
-/
theorem operativeTargets_ne_of_kernelSeparation
    (X : Realization C S sem Rep N ℝ P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    (witness : KernelSeparationWitness X) :
    ∃ (observation : Observation P N ℝ)
      (leftWitness rightWitness : HiddenHodgeWitness X observation),
      operativeTarget X observation leftWitness ≠
        operativeTarget X observation rightWitness := by
  let observation : Observation P N ℝ :=
    (X.classifier.π witness.left, witness.input)
  let leftWitness : HiddenHodgeWitness X observation :=
    { representative := witness.left
      class_eq := rfl }
  let rightWitness : HiddenHodgeWitness X observation :=
    { representative := witness.right
      class_eq :=
        (samePublicClass_of_homotopyEquivalent X hInv
          witness.semanticEquivalence).symm }
  have hleftTarget :
      operativeTarget X observation leftWitness = witness.input := by
    exact congrArg WithLp.ofLp
      (HCP.operativeHarmonicComponent_eq_self_of_harmonic
        (X.laplacian witness.left) (WithLp.toLp 2 witness.input) witness.harmonic_left)
  refine ⟨observation, leftWitness, rightWitness, ?_⟩
  intro htargets
  have hrightTarget :
      operativeTarget X observation rightWitness = witness.input :=
    htargets.symm.trans hleftTarget
  have hrightHarmonic :=
    operativeTarget_is_harmonic X observation rightWitness
  rw [hrightTarget] at hrightHarmonic
  exact witness.not_harmonic_right hrightHarmonic

/--
A compatible family containing two distinct operative targets admits no
public solver exact on every member at their common observation.

The auxiliary input, including any oracle, is held fixed across members.
There is no running-time restriction on the solver or cardinality assumption
on the family. Every larger compatible family retaining the two witnesses
inherits the same exact-recovery obstruction.
-/
theorem no_solver_exactOnOperativeTarget_on_family
    (X : Realization C S sem Rep N ℝ P)
    (observation : Observation P N ℝ)
    (family : Set (HiddenHodgeWitness X observation))
    {leftWitness rightWitness : HiddenHodgeWitness X observation}
    (hleft : leftWitness ∈ family)
    (hright : rightWitness ∈ family)
    (htargets : operativeTarget X observation leftWitness ≠
      operativeTarget X observation rightWitness)
    {Aux : Type uAux} {solver : Solver Aux P N ℝ} {aux : Aux}
    (hexact : ∀ witness ∈ family,
      solver aux observation = operativeTarget X observation witness) : False := by
  exact htargets ((hexact leftWitness hleft).symm.trans (hexact rightWitness hright))

/-- No public solver can be exact on every operative target in an ambiguous fiber. -/
theorem no_solver_exactOnOperativeTarget_of_kernelSeparation
    (X : Realization C S sem Rep N ℝ P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    (witness : KernelSeparationWitness X)
    {Aux : Type uAux} {solver : Solver Aux P N ℝ} {aux : Aux}
    (hexact : SolverExactOnOperativeTarget X solver aux) : False := by
  obtain ⟨observation, leftWitness, rightWitness, htargets⟩ :=
    operativeTargets_ne_of_kernelSeparation X hInv witness
  exact no_solver_exactOnOperativeTarget_on_family X observation Set.univ
    (Set.mem_univ leftWitness) (Set.mem_univ rightWitness) htargets
    (solver := solver) (aux := aux) (fun compatible _ => hexact observation compatible)

/--
Even a correct explicit-lattice CVP oracle cannot resolve a supplied HCP
kernel-separation witness: it is auxiliary data, while the identical public
observation still fails to select the operative Hodge extension.
-/
theorem cvpOracle_insufficient_of_kernelSeparation
    {N : Type} [Fintype N]
    (X : Realization C S sem Rep N ℝ P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    (witness : KernelSeparationWitness X)
    (hOracle : ∃ O : _root_.CVP.Oracle N N, _root_.CVP.OracleCorrect O) :
    ¬ ∃ solver : Solver (_root_.CVP.Oracle N N) P N ℝ,
      ∀ O : _root_.CVP.Oracle N N, _root_.CVP.OracleCorrect O →
        SolverSoundOn X solver O ∧ SolverExactOnHarmonic X solver O := by
  rintro ⟨solver, hsolver⟩
  obtain ⟨O, hO⟩ := hOracle
  exact no_solver_on_kernelSeparation X hInv witness
    (hsolver O hO).1 (hsolver O hO).2

/--
Direct operative-target form of CVP-oracle insufficiency: a correct
known-lattice oracle cannot make one public output equal two distinct hidden
projections selected inside the same public fiber.
-/
theorem cvpOracle_insufficient_for_operativeTarget
    {N : Type} [Fintype N]
    (X : Realization C S sem Rep N ℝ P)
    (hInv : Helfer.ClosedFormulaInvariance sem)
    (witness : KernelSeparationWitness X)
    (hOracle : ∃ O : _root_.CVP.Oracle N N, _root_.CVP.OracleCorrect O) :
    ¬ ∃ solver : Solver (_root_.CVP.Oracle N N) P N ℝ,
      ∀ O : _root_.CVP.Oracle N N, _root_.CVP.OracleCorrect O →
        SolverExactOnOperativeTarget X solver O := by
  rintro ⟨solver, hsolver⟩
  obtain ⟨O, hO⟩ := hOracle
  exact no_solver_exactOnOperativeTarget_of_kernelSeparation X hInv witness
    (hsolver O hO)

end HomotopicalEncryption.HCPBridge

-- Legacy matrix-wide sanity model.
--
-- The solver below receives only a cochain and is required to work for every
-- matrix of the ambient size. It is retained as a generic contradiction test,
-- not as the concrete HCP public interface. The representative-indexed solver
-- consuming `(publicClass, cochain)` is `HomotopicalEncryption.HCPBridge.Solver` above.

/-- Correctness surface for a solver that is explicitly given the operator. -/
def Hodge_Solver_Correct {N : Type} [Fintype N] {R : Type} [CommRing R]
  (solver : Matrix N N R → (N → R) → (N → R))
  (Δ : Matrix N N R) (b : N → R) : Prop :=
  MatrixIsHarmonic Δ (solver Δ b)

-- Presented-linear-image realization.
-- This is deliberately not stated as a discrete-CVP reduction.

theorem Hodge_GeneratedSubspace_Reduction
  {n : Type} [Fintype n] [DecidableEq n]
  {R : Type} [Field R] -- Using Field for dimension/basis arguments
  (solver : Matrix n n R → (n → R) → (n → R))
  -- Assumption: The solver works for any valid Hodge instance constructed from the system
  (h_solver : ∀ (Δ : Matrix n n R) (b : n → R),
    MatrixIsHarmonic Δ (solver Δ b)) :
  ∀ (B : Matrix n n R) (t : n → R),
    ∃ (Δ : Matrix n n R),
      -- The constructed Δ has kernel equal to the field-linear image of B.
      (∀ v, Matrix.mulVec Δ v = 0 ↔ ∃ x, Matrix.mulVec B x = v) ∧
      -- The solver output lies in that image.
      (∃ x, Matrix.mulVec B x = solver Δ t) :=
  by
    -- Let's choose any matrix $B$ and vector $t$.
    intro B t
    -- We need to find a matrix $\Delta$ such that the kernel of $\Delta$ is exactly the range of $B$.
    have h_ker_range : ∃ Δ : Matrix n n R, LinearMap.ker (Matrix.mulVecLin Δ) = LinearMap.range (Matrix.mulVecLin B) := by
      -- By the properties of linear algebra, we can find such a matrix $\Delta$.
      have h_ker_range : ∀ (V : Submodule R (n → R)), ∃ Δ : Matrix n n R, LinearMap.ker (Matrix.mulVecLin Δ) = V := by
        intro V;
        -- Let $W$ be a complement of $V$ in $R^n$, so $R^n = V \oplus W$.
        obtain ⟨W, hW⟩ : ∃ W : Submodule R (n → R), IsCompl V W := by
          exact Submodule.exists_isCompl V;
        -- Let $P$ be the projection onto $W$ along $V$.
        obtain ⟨P, hP⟩ : ∃ P : (n → R) →ₗ[R] (n → R), (∀ v ∈ V, P v = 0) ∧ (∀ w ∈ W, P w = w) := by
          have h_proj : ∀ v : n → R, ∃! p : n → R, p ∈ W ∧ v - p ∈ V := by
            intro v
            obtain ⟨p, hp⟩ : ∃ p : n → R, p ∈ W ∧ v - p ∈ V := by
              have := Submodule.mem_sup.mp ( show v ∈ V ⊔ W from by rw [ hW.sup_eq_top ] ; exact Submodule.mem_top ) ; aesop;
            refine' ⟨ p, hp, fun q hq => _ ⟩;
            have h_eq : q - p ∈ V ∧ q - p ∈ W := by
              exact ⟨ by simpa using V.sub_mem hp.2 hq.2, by simpa using W.sub_mem hq.1 hp.1 ⟩;
            have := hW.disjoint.le_bot h_eq; simp_all +decide [ sub_eq_zero ] ;
          choose P hP₁ hP₂ using h_proj;
          refine' ⟨ { toFun := P, map_add' := _, map_smul' := _ }, _, _ ⟩;
          all_goals norm_num at *;
          · intro x y; specialize hP₂ ( x + y ) ( P x + P y ) ; simp_all +decide [ Submodule.add_mem_iff_right ] ;
            exact Eq.symm ( hP₂ ( by simpa [ add_sub_add_comm ] using Submodule.add_mem _ ( hP₁ x |>.2 ) ( hP₁ y |>.2 ) ) );
          · intro m x; specialize hP₂ ( m • x ) ( m • P x ) ; simp_all +decide [ Submodule.smul_mem ] ;
            exact Eq.symm ( hP₂ ( by simpa only [ smul_sub ] using Submodule.smul_mem _ _ ( hP₁ x |>.2 ) ) );
          · intro v hv; specialize hP₂ v 0; aesop;
          · exact fun w hw => Eq.symm (hP₂ w w ⟨hw, by simp⟩)
        -- Let $\Delta$ be the matrix representation of $P$.
        obtain ⟨Δ, hΔ⟩ : ∃ Δ : Matrix n n R, P = Matrix.mulVecLin Δ := by
          use LinearMap.toMatrix' P;
          ext; simp +decide [ LinearMap.toMatrix' ];
        refine' ⟨ Δ, le_antisymm _ _ ⟩ <;> intro v hv <;> simp_all +decide;
        -- Since $v \in \ker(\Delta)$, we can write $v = v_1 + v_2$ where $v_1 \in V$ and $v_2 \in W$.
        obtain ⟨v1, v2, hv1, hv2, hv_eq⟩ : ∃ v1 ∈ V, ∃ v2 ∈ W, v = v1 + v2 := by
          have := hW.sup_eq_top;
          simpa [ eq_comm ] using Submodule.mem_sup.mp ( this.symm ▸ Submodule.mem_top : v ∈ V ⊔ W );
        simp_all +decide [ Matrix.mulVec_add ];
      exact h_ker_range _;
    obtain ⟨Δ, hΔ⟩ := h_ker_range
    have hΔ_pointwise :
        ∀ v, Matrix.mulVec Δ v = 0 ↔ ∃ x, Matrix.mulVec B x = v := by
      intro v
      have hv := SetLike.ext_iff.mp hΔ v
      simpa only [LinearMap.mem_ker, LinearMap.mem_range, Matrix.mulVecLin_apply] using hv
    refine ⟨Δ, hΔ_pointwise, ?_⟩
    exact (hΔ_pointwise (solver Δ t)).mp (h_solver Δ t)

/-
Theorem showing that the harmonic property depends on the Laplacian (Ambiguity).
-/
theorem Hodge_Ambiguity
  {n : Type} [Fintype n] [DecidableEq n]
  {R : Type} [Field R] [DecidableEq R]
  (h_dim : Fintype.card n ≥ 2) :
  ∃ (Δ₁ Δ₂ : Matrix n n R) (b : n → R),
    (∃ h₁, MatrixIsHarmonic Δ₁ h₁ ∧ h₁ = b) ∧ -- b is harmonic for Δ₁ (so projection is b)
    (¬ ∃ h₂, MatrixIsHarmonic Δ₂ h₂ ∧ h₂ = b) -- b is NOT harmonic for Δ₂
    :=
  by
    norm_num [ MatrixIsHarmonic ] at *;
    -- Let's choose any two distinct elements $i, j \in n$.
    obtain ⟨i, j, hij⟩ : ∃ i j : n, i ≠ j := by
      exact Fintype.one_lt_card_iff.mp h_dim;
    refine' ⟨ 0, Matrix.diagonal ( fun x => if x = i then 1 else 0 ), fun x => if x = i then 1 else 0, _, _ ⟩ <;> simp +decide [ funext_iff, Matrix.mulVec ]

/-
Proof of Hodge_Ambiguity using zero and identity matrices.
-/
theorem Hodge_Ambiguity_Proof
  {n : Type} [Fintype n] [DecidableEq n]
  {R : Type} [Field R] [DecidableEq R]
  (h_dim : Fintype.card n ≥ 2) :
  ∃ (Δ₁ Δ₂ : Matrix n n R) (b : n → R),
    (∃ h₁, MatrixIsHarmonic Δ₁ h₁ ∧ h₁ = b) ∧
    (¬ ∃ h₂, MatrixIsHarmonic Δ₂ h₂ ∧ h₂ = b) := by
  exact Hodge_Ambiguity h_dim

/--
The constant public projection realizes the Hodge ambiguity as an ambiguity
inside one public equivalence class.
-/
theorem constantPublicProjection_publicCompatibleHodgeAmbiguity
  {n : Type} [Fintype n] [DecidableEq n]
  {R : Type} [Field R] [DecidableEq R]
  (h_dim : Fintype.card n ≥ 2) :
  PublicCompatibleHodgeAmbiguity (N := n) (R := R) (P := Unit)
    (fun _ : Matrix n n R => ()) := by
  obtain ⟨Δ₁, Δ₂, b, hb₁, hb₂⟩ := Hodge_Ambiguity (n := n) (R := R) h_dim
  exact ⟨Δ₁, Δ₂, b, rfl, hb₁, hb₂⟩

/--
Concrete kernel-ambiguity witness for the maximally lossy public projection.

If the public projection is constant, all hidden operators are publicly
compatible. `Hodge_Ambiguity` supplies two compatible operators whose harmonic
behavior differs on the same public cochain, so their kernels cannot coincide.
-/
theorem constantPublicProjection_kernelAmbiguous
  {n : Type} [Fintype n] [DecidableEq n]
  {R : Type} [Field R] [DecidableEq R]
  (h_dim : Fintype.card n ≥ 2) :
  KernelAmbiguous (N := n) (R := R) (P := Unit)
    (fun _ : Matrix n n R => ()) := by
  exact kernelAmbiguous_of_publicCompatibleHodgeAmbiguity
    (constantPublicProjection_publicCompatibleHodgeAmbiguity (n := n) (R := R) h_dim)

/-- The constant public projection is lossy in every nontrivial dimension. -/
theorem constantPublicProjection_lossy
  {n : Type} [Fintype n] [DecidableEq n]
  {R : Type} [Field R] [DecidableEq R]
  (h_dim : Fintype.card n ≥ 2) :
  LossyPublicProjection (N := n) (R := R) (P := Unit)
    (fun _ : Matrix n n R => ()) := by
  exact kernelAmbiguous_implies_lossy
    (constantPublicProjection_kernelAmbiguous (n := n) (R := R) h_dim)

/-
For every matrix B, there exists a matrix Δ whose kernel is exactly the image of B.
-/
lemma exists_matrix_ker_eq_range {n : Type} [Fintype n] [DecidableEq n] {R : Type} [Field R] [DecidableEq R] (B : Matrix n n R) :
  ∃ (Δ : Matrix n n R), ∀ v, Matrix.mulVec Δ v = 0 ↔ ∃ x, Matrix.mulVec B x = v := by
  -- Let V be the image of B (as a linear map). V is a subspace of R^n. Since R is a field, every subspace is the kernel of some linear map.
  obtain ⟨f, hf⟩ : ∃ f : (n → R) →ₗ[R] (n → R), LinearMap.ker f = Submodule.map (Matrix.mulVecLin B) ⊤ := by
    -- By the existence of a basis for any subspace, we can construct a linear map whose kernel is exactly the image of B.
    have h_basis : ∀ (V : Submodule R (n → R)), ∃ f : (n → R) →ₗ[R] (n → R), LinearMap.ker f = V := by
      -- Let $V$ be a subspace of $R^n$. We can construct a linear map whose kernel is exactly $V$.
      intro V
      obtain ⟨W, hW⟩ : ∃ W : Submodule R (n → R), V ⊔ W = ⊤ ∧ V ⊓ W = ⊥ := by
        obtain ⟨ W, hW ⟩ := Submodule.exists_isCompl V;
        exact ⟨ W, hW.sup_eq_top, hW.inf_eq_bot ⟩;
      -- Define the linear map $f : R^n \to R^n$ by $f(v) = w$, where $v = v_1 + w$ with $v_1 \in V$ and $w \in W$.
      obtain ⟨f, hf⟩ : ∃ f : (n → R) →ₗ[R] (n → R), ∀ v : n → R, f v ∈ W ∧ v - f v ∈ V := by
        have h_decomp : ∀ v : n → R, ∃! p : n → R, p ∈ W ∧ v - p ∈ V := by
          intro v
          obtain ⟨p, hp⟩ : ∃ p : n → R, p ∈ W ∧ v - p ∈ V := by
            have := Submodule.mem_sup.mp ( show v ∈ V ⊔ W from hW.1.symm ▸ Submodule.mem_top ) ; aesop;
          refine' ⟨ p, hp, fun q hq => _ ⟩;
          have h_eq : q - p ∈ V ⊓ W := by
            exact ⟨ by simpa using V.sub_mem hp.2 hq.2, by simpa using W.sub_mem hq.1 hp.1 ⟩;
          simp_all +decide [ Submodule.eq_bot_iff ];
          exact sub_eq_zero.mp ( hW.2 _ h_eq.1 h_eq.2 );
        choose f hf₁ hf₂ using h_decomp;
        refine' ⟨ { toFun := f, map_add' := _, map_smul' := _ }, hf₁ ⟩ <;> intros <;> simp_all +decide;
        · rw [ ← hf₂ ];
          · exact Submodule.add_mem _ ( hf₁ _ |>.1 ) ( hf₁ _ |>.1 );
          · simpa only [ add_sub_add_comm ] using V.add_mem ( hf₁ _ |>.2 ) ( hf₁ _ |>.2 );
        · rw [ ← hf₂ ];
          · exact Submodule.smul_mem _ _ ( hf₁ _ |>.1 );
          · simpa only [ smul_sub ] using Submodule.smul_mem _ _ ( hf₁ _ |>.2 );
      refine' ⟨ f, le_antisymm _ _ ⟩ <;> intro v hv <;> simp_all +decide [ Submodule.eq_bot_iff ];
      · simpa [ hv ] using hf v |>.2;
      · exact hW.2 _ ( by simpa using hf v |>.2 |> fun h => by simpa using V.sub_mem hv h ) ( hf v |>.1 );
    exact h_basis _;
  -- Let Δ be the matrix representation of f.
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Matrix n n R, ∀ v : n → R, f v = Δ.mulVec v := by
    exact ⟨ f.toMatrix', fun v => by simp +decide ⟩;
  simp_all +decide [ SetLike.ext_iff, LinearMap.mem_ker ];
  use Δ

/-
Formal verification that a solver harmonic for every presented operator returns
an element of a generated linear subspace after that subspace is realized as a
kernel. This theorem does not concern the discrete lattice `B ℤ^n`.
-/
theorem Hodge_GeneratedSubspace_Reduction_Proof
  {n : Type} [Fintype n] [DecidableEq n]
  {R : Type} [Field R] [DecidableEq R]
  (solver : Matrix n n R → (n → R) → (n → R))
  (h_solver : ∀ (Δ : Matrix n n R) (b : n → R),
    MatrixIsHarmonic Δ (solver Δ b)) :
  ∀ (B : Matrix n n R) (t : n → R),
    ∃ (Δ : Matrix n n R),
      (∀ v, Matrix.mulVec Δ v = 0 ↔ ∃ x, Matrix.mulVec B x = v) ∧
      (∃ x, Matrix.mulVec B x = solver Δ t) := by
  intro B t
  obtain ⟨Δ, hΔ⟩ := exists_matrix_ker_eq_range B
  use Δ
  constructor
  · exact hΔ
  · have h_harm := h_solver Δ t
    rw [MatrixIsHarmonic] at h_harm
    rw [hΔ] at h_harm
    exact h_harm

/--
Every cochain admits mutually orthogonal harmonic, exact, and coexact parts.
Their uniqueness is proved separately by `Hodge_Decomposition_unique`.
-/
theorem Hodge_Decomposition_Theorem
  {n m k : Type} [Fintype n] [Fintype m] [Fintype k]
  [DecidableEq n] [DecidableEq m] [DecidableEq k]
  (d_prev : Matrix m n Real)
  (d_next : Matrix k m Real)
  (h_complex : d_next * d_prev = 0) :
  let d_prev_adj := d_prev.transpose
  let d_next_adj := d_next.transpose
  let Δ := d_prev * d_prev_adj + d_next_adj * d_next
  ∀ (b : m → Real),
    ∃ (h : m → Real) (e1 : m → Real) (e2 : m → Real),
      b = h + e1 + e2 ∧
      MatrixIsHarmonic Δ h ∧
      (∃ x, e1 = Matrix.mulVec d_prev x) ∧
      (∃ y, e2 = Matrix.mulVec d_next_adj y) ∧
      -- Orthogonality
      dotProduct h e1 = 0 ∧
      dotProduct h e2 = 0 ∧
      dotProduct e1 e2 = 0 := by
  intro d_prev_adj d_next_adj Δ b;
  -- Let $h$ be the harmonic part of $b$, i.e., $h = b - e1 - e2$ where $e1 \in \text{im}(d_{\text{prev}})$ and $e2 \in \text{im}(d_{\text{next}}^*)$.
  obtain ⟨h, e1, e2, he1, he2, hh⟩ : ∃ h e1 e2 : m → ℝ, b = h + e1 + e2 ∧ e1 ∈ Submodule.map (Matrix.mulVecLin d_prev) ⊤ ∧ e2 ∈ Submodule.map (Matrix.mulVecLin d_next_adj) ⊤ ∧ h ∈ LinearMap.ker (Matrix.mulVecLin Δ) := by
    -- By definition of $Δ$, we know that its kernel is the orthogonal complement of the range of $Δ$.
    have h_kernel : LinearMap.ker (Matrix.mulVecLin Δ) ⊔ (Submodule.map (Matrix.mulVecLin d_prev) ⊤ + Submodule.map (Matrix.mulVecLin d_next_adj) ⊤) = ⊤ := by
      refine' Submodule.eq_top_iff'.mpr _;
      intro x
      have h_decomp : x ∈ LinearMap.ker (Matrix.mulVecLin Δ) ⊔ (LinearMap.range (Matrix.mulVecLin Δ)) := by
        have h_decomp : LinearMap.ker (Matrix.mulVecLin Δ) ⊔ LinearMap.range (Matrix.mulVecLin Δ) = ⊤ := by
          have h_self_adjoint : Matrix.IsHermitian Δ := by
            change (d_prev * d_prev.transpose + d_next.transpose * d_next).IsHermitian
            simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
              (Matrix.isHermitian_mul_conjTranspose_self d_prev).add
                (Matrix.isHermitian_conjTranspose_mul_self d_next)
          have h_decomp : ∀ x : m → ℝ, x ∈ LinearMap.ker (Matrix.mulVecLin Δ) ⊔ LinearMap.range (Matrix.mulVecLin Δ) := by
            intro x
            have h_decomp : x = ∑ i,
                (h_self_adjoint.eigenvectorBasis.repr (WithLp.toLp 2 x) i) •
                  (h_self_adjoint.eigenvectorBasis i).ofLp := by
              have hcoords := congrArg (fun y : EuclideanSpace ℝ m => y.ofLp)
                (h_self_adjoint.eigenvectorBasis.sum_repr (WithLp.toLp 2 x))
              simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_toLp] using
                hcoords.symm
            rw [ h_decomp ];
            refine' Submodule.sum_mem _ fun i _ => _;
            by_cases hi : h_self_adjoint.eigenvalues i = 0;
            · have h_eigenvalue_zero : Δ.mulVec (h_self_adjoint.eigenvectorBasis i) = 0 := by
                have := h_self_adjoint.mulVec_eigenvectorBasis i; simp +decide [ hi ] at this; exact this;
              exact Submodule.mem_sup_left
                (by simp [Matrix.mulVecLin_apply, Matrix.mulVec_smul, h_eigenvalue_zero]);
            · have h_eigenvalue : Δ.mulVec (h_self_adjoint.eigenvectorBasis i) = h_self_adjoint.eigenvalues i • h_self_adjoint.eigenvectorBasis i := by
                convert h_self_adjoint.mulVec_eigenvectorBasis i using 1;
              have h_eigenvalue : (h_self_adjoint.eigenvectorBasis i).ofLp ∈
                  LinearMap.range (Matrix.mulVecLin Δ) := by
                use (1 / h_self_adjoint.eigenvalues i) •
                  (h_self_adjoint.eigenvectorBasis i).ofLp
                simp [Matrix.mulVecLin_apply, Matrix.mulVec_smul, hi, h_eigenvalue,
                  smul_smul]
              exact Submodule.mem_sup_right ( Submodule.smul_mem _ _ h_eigenvalue );
          exact eq_top_iff.mpr fun x hx => h_decomp x;
        aesop;
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h_decomp
      refine Submodule.mem_sup.mpr ⟨y, hy, z, ?_, hyz⟩
      obtain ⟨w, rfl⟩ := hz
      apply Submodule.mem_sup.mpr
      refine ⟨d_prev.mulVec (d_prev_adj.mulVec w), ?_,
        d_next_adj.mulVec (d_next.mulVec w), ?_, ?_⟩
      · exact Submodule.mem_map.mpr ⟨d_prev_adj.mulVec w, trivial, rfl⟩
      · exact Submodule.mem_map.mpr ⟨d_next.mulVec w, trivial, rfl⟩
      · simp only [Δ, Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.mulVec_mulVec]
    have hb : b ∈ LinearMap.ker (Matrix.mulVecLin Δ) ⊔
        (Submodule.map (Matrix.mulVecLin d_prev) ⊤ +
          Submodule.map (Matrix.mulVecLin d_next_adj) ⊤) := by
      rw [h_kernel]
      trivial
    obtain ⟨h, hh, e, he, hhe⟩ := Submodule.mem_sup.mp hb
    obtain ⟨e1, he1, e2, he2, he12⟩ := Submodule.mem_sup.mp he
    refine ⟨h, e1, e2, ?_, he1, he2, hh⟩
    calc
      b = h + e := hhe.symm
      _ = h + (e1 + e2) := congrArg (fun y => h + y) he12.symm
      _ = h + e1 + e2 := (add_assoc _ _ _).symm
  refine' ⟨ h, e1, e2, he1, _, _, _, _ ⟩ <;> simp_all +decide [ MatrixIsHarmonic ];
  · tauto;
  · grind;
  · -- Since $h$ is in the kernel of $\Delta$, we have $\Delta h = 0$, which implies $d_{\text{prev}}^* h = 0$ and $d_{\text{next}} h = 0$.
    have h_kernel : d_prev_adj.mulVec h = 0 ∧ d_next.mulVec h = 0 := by
      have h_kernel : (d_prev_adj.mulVec h) ⬝ᵥ (d_prev_adj.mulVec h) + (d_next.mulVec h) ⬝ᵥ (d_next.mulVec h) = 0 := by
        have h_kernel : (d_prev * d_prev_adj + d_next_adj * d_next).mulVec h = d_prev.mulVec (d_prev_adj.mulVec h) + d_next_adj.mulVec (d_next.mulVec h) := by
          simp +decide [ Matrix.add_mulVec ];
        have h_kernel : (d_prev_adj.mulVec h) ⬝ᵥ (d_prev_adj.mulVec h) + (d_next.mulVec h) ⬝ᵥ (d_next.mulVec h) = (d_prev.mulVec (d_prev_adj.mulVec h)) ⬝ᵥ h + (d_next_adj.mulVec (d_next.mulVec h)) ⬝ᵥ h := by
          simp +zetaDelta at *;
          simp +decide [ Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec, dotProduct_comm ];
        have h_kernel : (d_prev.mulVec (d_prev_adj.mulVec h) + d_next_adj.mulVec (d_next.mulVec h)) ⬝ᵥ h = 0 := by
          rw [ ← ‹ ( d_prev * d_prev_adj + d_next_adj * d_next ).mulVec h = d_prev.mulVec ( d_prev_adj.mulVec h ) + d_next_adj.mulVec ( d_next.mulVec h ) ›, hh.2, zero_dotProduct ]
        simp_all +decide;
      have h_kernel : (d_prev_adj.mulVec h) ⬝ᵥ (d_prev_adj.mulVec h) = 0 ∧ (d_next.mulVec h) ⬝ᵥ (d_next.mulVec h) = 0 := by
        exact ⟨ by nlinarith only [ h_kernel, show 0 ≤ d_prev_adj.mulVec h ⬝ᵥ d_prev_adj.mulVec h from Finset.sum_nonneg fun _ _ => mul_self_nonneg _, show 0 ≤ d_next.mulVec h ⬝ᵥ d_next.mulVec h from Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ], by nlinarith only [ h_kernel, show 0 ≤ d_prev_adj.mulVec h ⬝ᵥ d_prev_adj.mulVec h from Finset.sum_nonneg fun _ _ => mul_self_nonneg _, show 0 ≤ d_next.mulVec h ⬝ᵥ d_next.mulVec h from Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ] ⟩;
      simp_all +decide;
    -- Since $e1 \in \text{im}(d_{\text{prev}})$, we have $e1 = d_{\text{prev}} x$ for some $x$.
    obtain ⟨x, hx⟩ : ∃ x : n → ℝ, e1 = d_prev.mulVec x := by
      tauto;
    -- Since $e2 \in \text{im}(d_{\text{next}}^*)$, we have $e2 = d_{\text{next}}^* y$ for some $y$.
    obtain ⟨y, hy⟩ : ∃ y : k → ℝ, e2 = d_next_adj.mulVec y := by
      grind +ring
    simp_all +decide [ Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec ];
    simp_all +decide [ ← Matrix.mulVec_transpose ];
    aesop

/--
Two harmonic/exact/coexact decompositions of the same real matrix cochain
agree componentwise. The complex equation makes the exact and coexact
subspaces orthogonal; no additional orthogonality hypotheses are required.
-/
theorem Hodge_Decomposition_unique
    {n m k : Type} [Fintype n] [Fintype m] [Fintype k]
    [DecidableEq n] [DecidableEq m] [DecidableEq k]
    (d_prev : Matrix m n ℝ) (d_next : Matrix k m ℝ)
    (h_complex : d_next * d_prev = 0)
    {b h e1 e2 h' e1' e2' : m → ℝ}
    (hb : b = h + e1 + e2)
    (hh : MatrixIsHarmonic
      (d_prev * d_prev.transpose + d_next.transpose * d_next) h)
    (he1 : ∃ x, e1 = d_prev.mulVec x)
    (he2 : ∃ y, e2 = d_next.transpose.mulVec y)
    (hb' : b = h' + e1' + e2')
    (hh' : MatrixIsHarmonic
      (d_prev * d_prev.transpose + d_next.transpose * d_next) h')
    (he1' : ∃ x, e1' = d_prev.mulVec x)
    (he2' : ∃ y, e2' = d_next.transpose.mulVec y) :
    h = h' ∧ e1 = e1' ∧ e2 = e2' := by
  obtain ⟨x, rfl⟩ := he1
  obtain ⟨y, rfl⟩ := he2
  obtain ⟨x', rfl⟩ := he1'
  obtain ⟨y', rfl⟩ := he2'
  let a := h - h'
  let e := d_prev.mulVec (x - x')
  let c := d_next.transpose.mulVec (y - y')
  have hsum : a + e + c = 0 := by
    dsimp [a, e, c]
    simpa only [Matrix.mulVec_sub, add_sub_add_comm] using
      sub_eq_zero.mpr (hb.symm.trans hb')
  have ha : (d_prev * d_prev.transpose + d_next.transpose * d_next).mulVec a = 0 := by
    change (d_prev * d_prev.transpose + d_next.transpose * d_next).mulVec h = 0 at hh
    change (d_prev * d_prev.transpose + d_next.transpose * d_next).mulVec h' = 0 at hh'
    simp only [a, Matrix.mulVec_sub, hh, hh', sub_self]
  have henergy :
      d_prev.transpose.mulVec a ⬝ᵥ d_prev.transpose.mulVec a +
        d_next.mulVec a ⬝ᵥ d_next.mulVec a = 0 := by
    have hz := congrArg (fun v => a ⬝ᵥ v) ha
    simpa only [Matrix.add_mulVec, Matrix.mulVec_mulVec, dotProduct_add,
      Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_mul,
      Matrix.transpose_transpose,
      dotProduct_zero] using hz
  have hparts : d_prev.transpose.mulVec a = 0 ∧ d_next.mulVec a = 0 := by
    have hnonneg0 : 0 ≤ d_prev.transpose.mulVec a ⬝ᵥ d_prev.transpose.mulVec a :=
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    have hnonneg1 : 0 ≤ d_next.mulVec a ⬝ᵥ d_next.mulVec a :=
      Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    have hp := (add_eq_zero_iff_of_nonneg hnonneg0 hnonneg1).mp henergy
    exact ⟨dotProduct_self_eq_zero.mp hp.1, dotProduct_self_eq_zero.mp hp.2⟩
  have hae : a ⬝ᵥ e = 0 := by
    dsimp [e]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hparts.1,
      zero_dotProduct]
  have hac : a ⬝ᵥ c = 0 := by
    dsimp [c]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hparts.2,
      zero_dotProduct]
  have hec : e ⬝ᵥ c = 0 := by
    dsimp [e, c]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
      h_complex, Matrix.zero_mulVec, zero_dotProduct]
  have ha0 : a = 0 := by
    apply dotProduct_self_eq_zero.mp
    have hz := congrArg (fun v => a ⬝ᵥ v) hsum
    simpa only [dotProduct_add, hae, hac, add_zero, dotProduct_zero] using hz
  have he0 : e = 0 := by
    apply dotProduct_self_eq_zero.mp
    have hz := congrArg (fun v => e ⬝ᵥ v) hsum
    simpa only [dotProduct_add, ha0, dotProduct_zero, hec, zero_add, add_zero] using hz
  have hc0 : c = 0 := by
    simpa only [ha0, he0, zero_add] using hsum
  refine ⟨sub_eq_zero.mp ha0, ?_, ?_⟩
  · exact sub_eq_zero.mp (by simpa only [e, Matrix.mulVec_sub] using he0)
  · exact sub_eq_zero.mp (by simpa only [c, Matrix.mulVec_sub] using hc0)

/--
Public Hodge instance available to an attacker.

In the documented model, the public side exposes cochain/commitment-facing
data, hashes, and class handles. This file abstracts those public artifacts to
the observed cochain-facing datum `b : n → R`; the hidden Laplacian/fibration
is not given to the solver.
-/
def PublicHodgeInstance (n : Type) (R : Type) := n → R

/--
A public-data Hodge solver with arbitrary auxiliary information.

The auxiliary type is explicit so the ambiguity theorem can be proved without
conflating a field-linear kernel with a discrete lattice. The CVP corollary
below instantiates `Aux` with a genuine `CVP.Oracle`.
-/
def PublicHodgeSolver
    (Aux : Type) (n : Type) [Fintype n] (R : Type) [CommRing R] :=
  Aux → PublicHodgeInstance n R → (n → R)

/-- Soundness requirement: the solver outputs a harmonic vector for the hidden `Δ`. -/
def PublicHodgeSolverSound
    {Aux n : Type} [Fintype n] {R : Type} [CommRing R]
    (solver : PublicHodgeSolver Aux n R) (aux : Aux) : Prop :=
  ∀ (Δ : Matrix n n R) (b : PublicHodgeInstance n R),
    MatrixIsHarmonic Δ (solver aux b)

/--
Exactness requirement on already-harmonic inputs.

If the public cochain is already harmonic for the hidden `Δ`, a correct solver
should recover it unchanged.
-/
def PublicHodgeSolverExactOnHarmonic
    {Aux n : Type} [Fintype n] {R : Type} [CommRing R]
    (solver : PublicHodgeSolver Aux n R) (aux : Aux) : Prop :=
  ∀ (Δ : Matrix n n R) (b : PublicHodgeInstance n R),
    MatrixIsHarmonic Δ b → solver aux b = b

/--
If a public cochain `b` is already harmonic for `Δ`, exactness forces a public
solver to return `b` unchanged.
-/
lemma public_solver_eq_input_of_harmonic
  {Aux n : Type} [Fintype n] {R : Type} [CommRing R]
  {solver : PublicHodgeSolver Aux n R} {aux : Aux}
  (hexact : PublicHodgeSolverExactOnHarmonic solver aux)
  {Δ : Matrix n n R} {b : PublicHodgeInstance n R}
  (hb : MatrixIsHarmonic Δ b) :
  solver aux b = b := by
  exact hexact Δ b hb

/--
Core ambiguity contradiction for public-data-only Hodge solvers.

If the same public cochain is harmonic for one hidden Laplacian and not for
another, then a solver that is both sound and exact-on-harmonic cannot exist.
-/
lemma no_public_solver_on_ambiguous_input
  {Aux n : Type} [Fintype n] {R : Type} [CommRing R]
  {solver : PublicHodgeSolver Aux n R} {aux : Aux}
  (hsound : PublicHodgeSolverSound solver aux)
  (hexact : PublicHodgeSolverExactOnHarmonic solver aux)
  {Δ₁ Δ₂ : Matrix n n R} {b : PublicHodgeInstance n R}
  (hb₁ : ∃ h₁, MatrixIsHarmonic Δ₁ h₁ ∧ h₁ = b)
  (hb₂ : ¬ ∃ h₂, MatrixIsHarmonic Δ₂ h₂ ∧ h₂ = b) :
  False := by
  rcases hb₁ with ⟨h₁, hh₁_harm, hh₁_eq⟩
  have hb_harm₁ : MatrixIsHarmonic Δ₁ b := by simpa [hh₁_eq] using hh₁_harm
  have h_eq : solver aux b = b := public_solver_eq_input_of_harmonic hexact hb_harm₁
  have h_harm₂ : MatrixIsHarmonic Δ₂ (solver aux b) := hsound Δ₂ b
  exact hb₂ ⟨solver aux b, h_harm₂, h_eq⟩

/-- Hidden-operator ambiguity rules out a uniform public-data-only solver. -/
theorem no_uniform_public_hodge_solver
  {n : Type} [Fintype n] [DecidableEq n]
  {R : Type} [Field R] [DecidableEq R]
  (h_dim : Fintype.card n ≥ 2) :
  ¬ ∃ (solver : (n → R) → (n → R)),
    (∀ (Δ : Matrix n n R) (b : n → R),
      MatrixIsHarmonic Δ (solver b)) ∧
    (∀ (Δ : Matrix n n R) (b : n → R),
      MatrixIsHarmonic Δ b → solver b = b) := by
  intro h
  rcases h with ⟨solver, hsound, hexact⟩
  obtain ⟨Δ₁, Δ₂, b, hb₁, hb₂⟩ :=
    Hodge_Ambiguity (n := n) (R := R) h_dim
  rcases hb₁ with ⟨h₁, hh₁, rfl⟩
  have heq : solver h₁ = h₁ := hexact Δ₁ h₁ hh₁
  exact hb₂ ⟨solver h₁, hsound Δ₂ h₁, heq⟩

/--
Generic matrix-wide oracle-insufficiency sanity theorem.

This quantifies over every matrix and lets the solver see only the cochain. The
HCP-faithful theorem, indexed by admitted representatives and the actual public
class value, is `HomotopicalEncryption.HCPBridge.cvpOracle_insufficient_of_kernelSeparation`.
-/
theorem CVP_Oracle_Insufficient_For_Public_Hodge_Solving
  {n : Type} [Fintype n] [DecidableEq n]
  (h_dim : Fintype.card n ≥ 2) :
  (∃ O : _root_.CVP.Oracle n n, _root_.CVP.OracleCorrect O) →
  ¬ ∃ (solver : PublicHodgeSolver (_root_.CVP.Oracle n n) n ℝ),
    ∀ (O : _root_.CVP.Oracle n n), _root_.CVP.OracleCorrect O →
      PublicHodgeSolverSound solver O ∧
      PublicHodgeSolverExactOnHarmonic solver O := by
  classical
  intro hO_exists
  by_contra h
  obtain ⟨solver, hsolver⟩ := h
  obtain ⟨O, hO⟩ :
      ∃ O : _root_.CVP.Oracle n n, _root_.CVP.OracleCorrect O := hO_exists
  obtain ⟨hsound, hexact⟩ := hsolver O hO
  obtain ⟨Δ₁, Δ₂, b, hb₁, hb₂⟩ :=
    Hodge_Ambiguity (n := n) (R := ℝ) h_dim
  exact no_public_solver_on_ambiguous_input hsound hexact hb₁ hb₂

-- ═══════════════════════════════════════════════════════════════════════
-- Explicit HCP / discrete-CVP bridge
-- ═══════════════════════════════════════════════════════════════════════

/-- Regard the coordinate carrier used by `CVP` as its Euclidean space. -/
def cvpVectorAsEuclidean
    {m : Type} [Fintype m]
    (v : _root_.CVP.AmbientVector m) : EuclideanSpace ℝ m :=
  WithLp.toLp 2 v

/-- Forget the Euclidean norm structure while retaining the coordinates. -/
def cvpVectorOfEuclidean
    {m : Type} [Fintype m]
    (v : EuclideanSpace ℝ m) : _root_.CVP.AmbientVector m :=
  fun i => v i

/-- The coordinate-sum distance in `CVP` is the squared Euclidean norm. -/
theorem cvp_squaredEuclideanDistance_eq_norm_sq
    {m : Type} [Fintype m]
    (u v : _root_.CVP.AmbientVector m) :
    _root_.CVP.squaredEuclideanDistance u v =
      ‖cvpVectorAsEuclidean u - cvpVectorAsEuclidean v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [_root_.CVP.squaredEuclideanDistance, cvpVectorAsEuclidean,
    Real.norm_eq_abs, sq_abs]

private theorem matrix_harmonic_iff_projection_isHarmonic_coordinates
    {n : Type} [Fintype n] [DecidableEq n]
    (W : Submodule ℝ (EuclideanSpace ℝ n)) [W.HasOrthogonalProjection]
    (h : EuclideanSpace ℝ n) :
    MatrixIsHarmonic (_root_.laplacian W) h ↔ HomotopicalEncryption.Laplacian.IsHarmonic W h := by
  simp only [MatrixIsHarmonic, HomotopicalEncryption.Laplacian.IsHarmonic,
    HomotopicalEncryption.Laplacian.residualVector, WithLp.toLp_eq_zero]

/--
The data needed to compare Hodge projection with genuine discrete CVP.

`lattice` is the discrete set `B ℤⁿ`. `harmonicSubspace` is the real Hodge
subspace `W`; the final field says only that every lattice point lies in `W`.
It deliberately does not identify the real subspace `W` with the discrete
lattice.
-/
structure HarmonicCVPBridge
    (m n : Type) [Fintype m] [Fintype n] where
  lattice : _root_.CVP.ExplicitLattice m n
  harmonicSubspace : Submodule ℝ (EuclideanSpace ℝ m)
  latticeVector_mem :
    ∀ z : n → ℤ,
      cvpVectorAsEuclidean (_root_.CVP.latticeVector lattice z) ∈
        harmonicSubspace

namespace HarmonicCVPBridge

/-- Project a CVP target onto the Hodge subspace while retaining its coordinates. -/
def projectedTarget
    {m n : Type} [Fintype m] [Fintype n]
    (H : HarmonicCVPBridge m n)
    [H.harmonicSubspace.HasOrthogonalProjection]
    (t : _root_.CVP.AmbientVector m) : _root_.CVP.AmbientVector m :=
  cvpVectorOfEuclidean
    (H.harmonicSubspace.starProjection (cvpVectorAsEuclidean t))

/-- Package a bridge lattice and a target as a genuine discrete CVP instance. -/
def cvpInstance
    {m n : Type} [Fintype m] [Fintype n]
    (H : HarmonicCVPBridge m n)
    (t : _root_.CVP.AmbientVector m) : _root_.CVP.Instance m n :=
  ⟨H.lattice, t⟩

/-- Every point of the bridge lattice is harmonic for `Δ_W = I - P_W`. -/
theorem latticeVector_isHarmonic
    {m n : Type} [Fintype m] [Fintype n]
    (H : HarmonicCVPBridge m n)
    [H.harmonicSubspace.HasOrthogonalProjection]
    (z : n → ℤ) :
    MatrixIsHarmonic (_root_.laplacian H.harmonicSubspace)
      (_root_.CVP.latticeVector H.lattice z) := by
  exact (matrix_harmonic_iff_projection_isHarmonic_coordinates H.harmonicSubspace
    (cvpVectorAsEuclidean (_root_.CVP.latticeVector H.lattice z))).2
    (HomotopicalEncryption.Laplacian.isHarmonic_of_mem H.harmonicSubspace (H.latticeVector_mem z))

/-- The projected CVP target is the harmonic projection for `Δ_W`. -/
theorem projectedTarget_isHarmonic
    {m n : Type} [Fintype m] [Fintype n]
    (H : HarmonicCVPBridge m n)
    [H.harmonicSubspace.HasOrthogonalProjection]
    (t : _root_.CVP.AmbientVector m) :
    MatrixIsHarmonic (_root_.laplacian H.harmonicSubspace)
      (H.projectedTarget t) := by
  exact (matrix_harmonic_iff_projection_isHarmonic_coordinates H.harmonicSubspace
    (H.harmonicSubspace.starProjection (cvpVectorAsEuclidean t))).2
    (HomotopicalEncryption.Laplacian.harmonicProjection_isHarmonic H.harmonicSubspace
      (cvpVectorAsEuclidean t))

/--
Pythagorean bridge for a lattice point `v ∈ Λ ⊆ W`:

`‖t - v‖² = ‖t - P_W t‖² + ‖P_W t - v‖²`.

The first summand is independent of `v`; this is the geometric reason target
projection preserves the discrete closest-vector problem.
-/
theorem squaredDistance_projection_decomposition
    {m n : Type} [Fintype m] [Fintype n]
    (H : HarmonicCVPBridge m n)
    [H.harmonicSubspace.HasOrthogonalProjection]
    (t v : _root_.CVP.AmbientVector m)
    (hv : _root_.CVP.InExplicitLattice H.lattice v) :
    _root_.CVP.squaredEuclideanDistance t v =
      _root_.CVP.squaredEuclideanDistance t (H.projectedTarget t) +
      _root_.CVP.squaredEuclideanDistance (H.projectedTarget t) v := by
  rcases hv with ⟨z, rfl⟩
  rw [cvp_squaredEuclideanDistance_eq_norm_sq,
    cvp_squaredEuclideanDistance_eq_norm_sq,
    cvp_squaredEuclideanDistance_eq_norm_sq]
  let tE := cvpVectorAsEuclidean t
  let p := H.harmonicSubspace.starProjection tE
  let l := cvpVectorAsEuclidean (_root_.CVP.latticeVector H.lattice z)
  change ‖tE - l‖ ^ 2 = ‖tE - p‖ ^ 2 + ‖p - l‖ ^ 2
  have hl : l ∈ H.harmonicSubspace := H.latticeVector_mem z
  have hp : p ∈ H.harmonicSubspace :=
    H.harmonicSubspace.starProjection_apply_mem tE
  have hpl : p - l ∈ H.harmonicSubspace :=
    H.harmonicSubspace.sub_mem hp hl
  have horth : inner ℝ (tE - p) (p - l) = 0 :=
    H.harmonicSubspace.starProjection_inner_eq_zero tE (p - l) hpl
  have hpyth :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (tE - p) (p - l) horth
  have hsplit : tE - l = (tE - p) + (p - l) := by
    abel
  rw [hsplit]
  simpa [pow_two] using hpyth

/--
A vector is closest in the original CVP instance exactly when it is closest
after Hodge-projecting the target. This preserves the discrete search inside
`W`; it does not replace that search by the continuous projection itself.
-/
theorem isClosestLatticeVector_iff_projectedTarget
    {m n : Type} [Fintype m] [Fintype n]
    (H : HarmonicCVPBridge m n)
    [H.harmonicSubspace.HasOrthogonalProjection]
    (t v : _root_.CVP.AmbientVector m) :
    _root_.CVP.IsClosestLatticeVector H.lattice t v ↔
      _root_.CVP.IsClosestLatticeVector H.lattice (H.projectedTarget t) v := by
  constructor
  · rintro ⟨hv, hmin⟩
    refine ⟨hv, ?_⟩
    intro w hw
    have hvd := H.squaredDistance_projection_decomposition t v hv
    have hwd := H.squaredDistance_projection_decomposition t w hw
    have h := hmin w hw
    rw [hvd, hwd] at h
    exact (add_le_add_iff_left _).mp h
  · rintro ⟨hv, hmin⟩
    refine ⟨hv, ?_⟩
    intro w hw
    have hvd := H.squaredDistance_projection_decomposition t v hv
    have hwd := H.squaredDistance_projection_decomposition t w hw
    rw [hvd, hwd]
    have h := hmin w hw
    linarith

/-- Instance-level form of the explicit HCP/CVP bridge. -/
theorem solution_iff_projectedTarget
    {m n : Type} [Fintype m] [Fintype n]
    (H : HarmonicCVPBridge m n)
    [H.harmonicSubspace.HasOrthogonalProjection]
    (t v : _root_.CVP.AmbientVector m) :
    _root_.CVP.Solution (H.cvpInstance t) v ↔
      _root_.CVP.Solution (H.cvpInstance (H.projectedTarget t)) v := by
  exact H.isClosestLatticeVector_iff_projectedTarget t v

end HarmonicCVPBridge

/--
Concrete cellular-sheaf HCP/CVP endpoint.

For a sample built from an explicitly presented point of the intrinsic
harmonic lattice, the genuine discrete CVP solutions are exactly that encoded
point.  This specializes the generic projection bridge above to the actual
degree-one sheaf Hodge Laplacian and its integral stalk structure.
-/
theorem concreteSheafHCP_CVP_solution_iff_message
    {Vertex Edge Face Rank : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face] [Fintype Rank]
    {X : HomotopicalEncryption.Sheaf.OrientedTwoComplex Vertex Edge Face}
    {F : HomotopicalEncryption.Sheaf.CellularSheaf X}
    {I : HomotopicalEncryption.Sheaf.CellularSheaf.IntegralStructure F}
    (H : HomotopicalEncryption.Sheaf.CellularSheaf.HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ)
    (opening : HomotopicalEncryption.Sheaf.CellularSheaf.HodgeNoise F)
    (v : _root_.CVP.AmbientVector
      (HomotopicalEncryption.Sheaf.CellularSheaf.TotalCoord Edge F.edgeDim)) :
    _root_.CVP.Solution (H.cvpInstance (H.encrypt z opening)) v ↔
      v = (H.point z).1 :=
  H.solution_cvpInstance_iff_eq_point z opening v

/-- Constructed cellular-sheaf HCP samples have a unique discrete CVP answer. -/
theorem concreteSheafHCP_CVP_existsUnique
    {Vertex Edge Face Rank : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face] [Fintype Rank]
    {X : HomotopicalEncryption.Sheaf.OrientedTwoComplex Vertex Edge Face}
    {F : HomotopicalEncryption.Sheaf.CellularSheaf X}
    {I : HomotopicalEncryption.Sheaf.CellularSheaf.IntegralStructure F}
    (H : HomotopicalEncryption.Sheaf.CellularSheaf.HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ)
    (opening : HomotopicalEncryption.Sheaf.CellularSheaf.HodgeNoise F) :
    ∃! v, _root_.CVP.Solution (H.cvpInstance (H.encrypt z opening)) v :=
  H.existsUnique_solution_cvpInstance z opening

/- Verification of the closest-harmonic comparison surface. -/
/-- A harmonic vector closest to the input among all harmonic vectors. -/
def ClosestHarmonicSolution
  {n : Type} [Fintype n]
  (Δ : Matrix n n Real)
  (b h : n → Real) : Prop :=
  MatrixIsHarmonic Δ h ∧
    ∀ v, MatrixIsHarmonic Δ v → dist b h ≤ dist b v

/-- Projection-model closest-harmonic solution using the canonical predicate. -/
def ProjectionClosestHarmonicSolution
  {n : Type} [Fintype n] [DecidableEq n]
  (W : Submodule ℝ (EuclideanSpace ℝ n))
  [W.HasOrthogonalProjection]
  (b h : EuclideanSpace ℝ n) : Prop :=
  HomotopicalEncryption.Laplacian.IsHarmonic W h ∧
    ∀ v, HomotopicalEncryption.Laplacian.IsHarmonic W v → dist b h ≤ dist b v

/--
The matrix-level harmonic predicate agrees with the canonical projection-model
predicate for `Δ_W = I - P_W`.
-/
theorem matrix_harmonic_iff_projection_isHarmonic
  {n : Type} [Fintype n] [DecidableEq n]
  (W : Submodule ℝ (EuclideanSpace ℝ n))
  [W.HasOrthogonalProjection]
  (h : EuclideanSpace ℝ n) :
  MatrixIsHarmonic (_root_.laplacian W) h ↔
    HomotopicalEncryption.Laplacian.IsHarmonic W h := by
  exact matrix_harmonic_iff_projection_isHarmonic_coordinates W h

theorem Hodge_Projection_Is_ClosestHarmonic
  {n : Type} [Fintype n] [DecidableEq n]
  (Δ : Matrix n n Real)
  (b : n → Real)
  (h : n → Real)
  (h_harmonic : MatrixIsHarmonic Δ h)
  (h_closest : ∀ h', MatrixIsHarmonic Δ h' → dist b h ≤ dist b h') :
  ClosestHarmonicSolution Δ b h := by
  exact ⟨h_harmonic, fun v hv => h_closest v hv⟩

/--
The Hodge harmonic projection is closest-harmonic once the closest-section
property has been supplied.
-/
theorem harmonicProjection_is_closestHarmonic
  {n : Type} [Fintype n] [DecidableEq n]
  (W : Submodule ℝ (EuclideanSpace ℝ n))
  [W.HasOrthogonalProjection]
  (b : EuclideanSpace ℝ n)
  (h_closest :
    ∀ v,
      HomotopicalEncryption.Laplacian.IsHarmonic W v →
        dist b (HomotopicalEncryption.Laplacian.harmonicProjection W b) ≤ dist b v) :
  ProjectionClosestHarmonicSolution W b
    (HomotopicalEncryption.Laplacian.harmonicProjection W b) := by
  exact ⟨HomotopicalEncryption.Laplacian.harmonicProjection_isHarmonic W b, h_closest⟩

-- ═══════════════════════════════════════════════════════════════════════
-- Fibration & Homotopy Equivalence
-- ═══════════════════════════════════════════════════════════════════════

/-
Grothendieck fibration and homotopy-equivalence interface.
-/
universe u v

open CategoryTheory

variable {E B : Type u} [Category.{v} E] [Category.{v} B]

/-- A morphism f : U ⟶ V in E is p-Cartesian. -/
def IsCartesianMorphism (p : E ⥤ B) {U V : E} (f : U ⟶ V) : Prop :=
  ∀ (W : E) (g : W ⟶ V) (h : p.obj W ⟶ p.obj U),
    p.map g = h ≫ p.map f →
    ∃! k : W ⟶ U, p.map k = h ∧ k ≫ f = g

/-- A functor p : E ⥤ B is a Grothendieck fibration. -/
class GrothendieckFibration (p : E ⥤ B) : Prop where
  has_cartesian_lifts : ∀ (V : E) (X : B) (α : X ⟶ p.obj V),
    ∃ (U : E) (h : p.obj U = X) (f : U ⟶ V),
      p.map f = eqToHom h ≫ α ∧ IsCartesianMorphism p f

/--
The total categories of two fibrations are categorically equivalent through
functors that commute strictly with the projections to the common base.

This is not Helfer's model-categorical homotopy equivalence of algebraic
interpretations; that notion is `HomotopicalEncryption.Helfer.HomotopyEquivalent`.
-/
def CategoricallyEquivalentFibrations
    {D : Type u} [Category.{v} D] (p : E ⥤ B) (q : D ⥤ B) : Prop :=
  ∃ (F : E ⥤ D) (G : D ⥤ E),
    p = F ⋙ q ∧ q = G ⋙ p ∧
    Nonempty (G ⋙ F ≅ Functor.id D) ∧
    Nonempty (F ⋙ G ≅ Functor.id E)

/-- Wrapper type for distinct copies. -/
structure Wrapper (n : ℕ) (E : Type u) where
  val : E

/-- The tagged copy retains the original category's actual morphisms. -/
instance (n : ℕ) (E : Type u) [Category.{v} E] : Category.{v} (Wrapper n E) where
  Hom X Y := X.val ⟶ Y.val
  id X := 𝟙 X.val
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- Functors between a category and its tagged copy. -/
def ToWrapper (n : ℕ) (E : Type u) [Category.{v} E] : E ⥤ Wrapper n E where
  obj X := ⟨X⟩
  map f := f
  map_id := by intro X; rfl
  map_comp := by intro X Y Z f g; rfl

def FromWrapper (n : ℕ) (E : Type u) [Category.{v} E] : Wrapper n E ⥤ E where
  obj W := W.val
  map f := f
  map_id := by intro W; rfl
  map_comp := by intro W Y Z f g; rfl

/-- Bundled Grothendieck fibration over B. -/
structure Fibration (B : Type u) [Category.{v} B] where
  E : Type u
  [str : Category.{v} E]
  p : E ⥤ B
  [is_fib : GrothendieckFibration p]

attribute [instance] Fibration.str Fibration.is_fib

/-- Construct a copy of a fibration tagged with a natural number. -/
def FibrationCopy (F : Fibration B) (n : ℕ) : Fibration B :=
  let E' := Wrapper n F.E
  let p' : E' ⥤ B := FromWrapper n F.E ⋙ F.p
  {
    E := E'
    p := p'
    is_fib := by
      constructor;
      intro V X α;
      obtain ⟨ U, hU, f, hf, hf' ⟩ := F.is_fib.has_cartesian_lifts V.val X α;
      refine' ⟨ ⟨ U ⟩, hU, _, _, _ ⟩;
      exact f;
      · exact hf;
      · intro W g h hg
        change ∃! k : W.val ⟶ U, F.p.map k = h ∧ k ≫ f = g
        exact hf' W.val g h hg
  }

/-- A tagged copy has a categorically equivalent total category over the base. -/
lemma copy_categoricallyEquivalent_thm (F : Fibration B) (n : ℕ) :
    CategoricallyEquivalentFibrations F.p (FibrationCopy F n).p := by
  change CategoricallyEquivalentFibrations F.p (FromWrapper n F.E ⋙ F.p)
  refine ⟨ToWrapper n F.E, FromWrapper n F.E, ?_, ?_, ?_, ?_⟩
  · -- F.p = ToWrapper ⋙ (FibrationCopy F n).p
    rfl
  · -- (FibrationCopy F n).p = FromWrapper ⋙ F.p
    rfl
  · refine ⟨NatIso.ofComponents (fun X => Iso.refl X) ?_⟩
    intro X Y f
    change f ≫ 𝟙 Y.val = 𝟙 X.val ≫ f
    exact (Category.comp_id (show X.val ⟶ Y.val from f)).trans
      (Category.id_comp (show X.val ⟶ Y.val from f)).symm
  · refine ⟨NatIso.ofComponents (fun X => Iso.refl X) ?_⟩
    intro X Y f
    change f ≫ 𝟙 Y = 𝟙 X ≫ f
    simp

/-- The induced functor composition is a Grothendieck fibration. -/
lemma FibrationCopy_is_Grothendieck (F : Fibration B) (n : ℕ) :
  GrothendieckFibration (FromWrapper n F.E ⋙ F.p) := by
    apply FibrationCopy F n |>.is_fib
