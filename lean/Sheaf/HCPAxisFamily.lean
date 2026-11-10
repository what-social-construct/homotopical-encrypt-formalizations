module

public import Sheaf.HarmonicLattice
public import Sheaf.Equivalence

@[expose] public section

/-!
# An integral cellular coexact axis family

Two genuine cellular sheaves have the same coordinate carriers and complementary
degree-one harmonic axes. Their integral harmonic messages and coexact noise
sum to the same observed vector, while their exact components are both zero.
These are mathematical samples, without a payload, snapshot, hash-binding or
public-view equality claim.
-/

set_option autoImplicit false

noncomputable section

namespace Hcrypt.Sheaf.HCPAxisFamily

open CellularSheaf
open scoped BigOperators RealInnerProductSpace

/-- One zero-dimensional vertex stalk, one two-dimensional edge stalk and one
one-dimensional face stalk; only the edge-to-face incidence is nonzero. -/
def complex : OrientedTwoComplex Unit Unit Unit where
  incidence01 _ _ := 0
  incidence12 _ _ := 1
  boundarySqZero _ _ := by simp

/-- Select one scalar coordinate of the edge stalk. -/
def restriction (axis : Fin 2) : Coord 2 →ₗ[ℝ] Coord 1 where
  toFun b := WithLp.toLp 2 fun _ => b axis
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual cellular sheaf with degree-one differential the selected row. -/
abbrev sheaf (axis : Fin 2) : CellularSheaf complex where
  vertexDim _ := 0
  edgeDim _ := 2
  faceDim _ := 1
  restrict01 _ _ := 0
  restrict12 _ _ := restriction axis
  restrict02 _ _ := 0
  restrictionComp _ _ _ h := False.elim (h rfl)

/-- The shared degree-one coordinate index. -/
abbrev Index := TotalCoord Unit (fun _ => 2)

/-- All presentations use this same Euclidean cochain carrier. -/
abbrev C1 := EuclideanSpace ℝ Index

/-- Standard coordinate unit vector in the shared edge cochain space. -/
def unitCochain (axis : Fin 2) : C1 := EuclideanSpace.single ⟨(), axis⟩ 1

@[simp] theorem unitCochain_apply (axis j : Fin 2) :
    unitCochain axis ⟨(), j⟩ = if j = axis then 1 else 0 := by
  simp [unitCochain, PiLp.single_apply, eq_comm]

@[simp] theorem delta0_eq_zero (axis : Fin 2) : (sheaf axis).delta0 = 0 := by
  apply LinearMap.ext
  intro a
  apply PiLp.ext
  rintro ⟨⟨⟩, j⟩
  simp [CellularSheaf.delta0, CellularSheaf.delta0At, assemble,
    complex, OrientedTwoComplex.incidence01Real]

@[simp] theorem delta1_apply (axis : Fin 2) (b : C1) :
    (sheaf axis).delta1 b ⟨(), 0⟩ = b ⟨(), axis⟩ := by
  simp [CellularSheaf.delta1, CellularSheaf.delta1At, assemble,
    complex, sheaf, restriction, component,
    OrientedTwoComplex.incidence12Real]
  rfl

theorem delta1_adjoint_eq (axis : Fin 2) (c : (sheaf axis).C2) :
    (sheaf axis).delta1.adjoint c =
      EuclideanSpace.single ⟨(), axis⟩ (c ⟨(), 0⟩) := by
  apply ext_inner_left ℝ
  intro b
  rw [LinearMap.adjoint_inner_right, EuclideanSpace.inner_single_right]
  simp [PiLp.inner_apply, Fintype.sum_sigma, delta1_apply]

@[simp] theorem degreeOneLaplacian_apply (axis : Fin 2) (b : C1) (j : Fin 2) :
    (sheaf axis).degreeOneLaplacian b ⟨(), j⟩ =
      if j = axis then b ⟨(), axis⟩ else 0 := by
  simp [CellularSheaf.degreeOneLaplacian, LinearMap.comp_apply,
    delta1_adjoint_eq, PiLp.single_apply,
    eq_comm]

theorem harmonic_iff (axis : Fin 2) (b : C1) :
    (sheaf axis).IsHarmonicOneCochain b ↔ b ⟨(), axis⟩ = 0 := by
  constructor
  · intro h
    have hcoord := congrArg (fun x : C1 => x ⟨(), axis⟩) h
    simpa [CellularSheaf.IsHarmonicOneCochain] using hcoord
  · intro h
    change (sheaf axis).degreeOneLaplacian b = 0
    apply PiLp.ext
    rintro ⟨⟨⟩, j⟩
    simp [h]

/-- Standard integer-coordinate stalk lattice, including the zero stalk. -/
def standardStalkLattice (n : ℕ) : StalkLattice n where
  presentation :=
    { basis := 1
      basis_injective := by
        intro x y h
        simpa only [Matrix.one_mulVec] using h }

theorem standardStalkLattice_contains_iff (n : ℕ) (x : Coord n) :
    (standardStalkLattice n).Contains x ↔
      ∃ z : Fin n → ℤ, ∀ i, x i = (z i : ℝ) := by
  change (∃ z : Fin n → ℤ,
    CVP.latticeVector (standardStalkLattice n).presentation z = ⇑x) ↔ _
  simp only [CVP.latticeVector, standardStalkLattice, Matrix.one_mulVec]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, fun i => (congrFun hz i).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, funext fun i => (hz i).symm⟩

/-- Coordinate selection preserves the standard integral stalk lattices. -/
theorem restriction_preserves (axis : Fin 2) :
    (standardStalkLattice 2).Preserves (standardStalkLattice 1)
      (restriction axis) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz⟩ := (standardStalkLattice_contains_iff 2 x).mp hx
  apply (standardStalkLattice_contains_iff 1 (restriction axis x)).mpr
  exact ⟨fun _ => z axis, fun _ => hz axis⟩

/-- A concrete integral structure on every member of the cellular family. -/
def integralStructure (axis : Fin 2) : IntegralStructure (sheaf axis) where
  vertexStalk _ := standardStalkLattice 0
  edgeStalk _ := standardStalkLattice 2
  faceStalk _ := standardStalkLattice 1
  restrict01_preserves _ _ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (standardStalkLattice 2).carrier.zero_mem
  restrict12_preserves _ _ := restriction_preserves axis
  restrict02_preserves _ _ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (standardStalkLattice 1).carrier.zero_mem

/-- The other coordinate is the harmonic axis. -/
def other (axis : Fin 2) : Fin 2 := ⟨1 - axis.val, by omega⟩

@[simp] theorem other_zero : other 0 = 1 := rfl
@[simp] theorem other_one : other 1 = 0 := rfl
@[simp] theorem other_ne (axis : Fin 2) : other axis ≠ axis := by
  fin_cases axis <;> decide

theorem unitCochain_integral (axis j : Fin 2) :
    unitCochain j ∈ (integralStructure axis).integralOneCochains := by
  intro e
  apply (standardStalkLattice_contains_iff 2 _).mpr
  refine ⟨fun i => if i = j then 1 else 0, ?_⟩
  intro i
  cases e
  change unitCochain j ⟨(), i⟩ = _
  simp [unitCochain_apply]

theorem other_unit_harmonic (axis : Fin 2) :
    (sheaf axis).IsHarmonicOneCochain (unitCochain (other axis)) := by
  rw [harmonic_iff]
  simp [Ne.symm (other_ne axis)]

/-- Nonzero integral harmonic message in the complementary coordinate. -/
def message (axis : Fin 2) : (integralStructure axis).harmonicOneLattice :=
  ⟨unitCochain (other axis), unitCochain_integral axis _, other_unit_harmonic axis⟩

/-- No exact noise, and one unit of coexact noise. -/
def opening (axis : Fin 2) : HodgeNoise (sheaf axis) where
  exactOpening := 0
  coexactOpening := EuclideanSpace.single ⟨(), 0⟩ 1

/-- Actual Hodge-encrypted samples with integral messages and structured noise. -/
def sample (axis : Fin 2) : HodgeEncryptedCochain (integralStructure axis) where
  message := message axis
  opening := opening axis

/-- Shared raw observation, with both coordinates equal to one. -/
def observed : C1 := unitCochain 0 + unitCochain 1

@[simp] theorem opening_exactComponent (axis : Fin 2) :
    (opening axis).exactComponent = 0 := by
  simp [HodgeNoise.exactComponent, opening]

@[simp] theorem opening_coexactComponent (axis : Fin 2) :
    (opening axis).coexactComponent = unitCochain axis := by
  simp [HodgeNoise.coexactComponent, opening, delta1_adjoint_eq,
    unitCochain]

theorem sample_observed (axis : Fin 2) : (sample axis).observed = observed := by
  change (message axis).1 + (opening axis).value = observed
  have hnoise : (opening axis).value = unitCochain axis := by
    change (opening axis).exactComponent + (opening axis).coexactComponent = _
    simp
  rw [hnoise]
  change unitCochain (other axis) + unitCochain axis = observed
  fin_cases axis
  · exact add_comm _ _
  · rfl

theorem sample_exactComponent (axis : Fin 2) :
    (sample axis).opening.exactComponent = 0 := opening_exactComponent axis

theorem sample_messages_ne : (sample 0).message.1 ≠ (sample 1).message.1 := by
  intro h
  have hc := congrArg (fun x : C1 => x ⟨(), 0⟩) h
  norm_num [sample, message, unitCochain_apply] at hc

theorem sample_noise_orthogonal (axis : Fin 2) :
    (sample axis).opening.value ∈ (sheaf axis).harmonicOneSubspace.orthogonal :=
  (sample axis).opening.value_mem_harmonic_orthogonal

theorem sample_projection (axis : Fin 2) :
    (sheaf axis).harmonicOneProjection observed = (sample axis).message.1 := by
  rw [← sample_observed axis]
  exact (sample axis).harmonicOneProjection_observed

/-- Matrix of the actual cellular Hodge operator in the common coordinate basis. -/
def laplacianMatrix (axis : Fin 2) : Matrix Index Index ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun Index ℝ).toBasis
    (EuclideanSpace.basisFun Index ℝ).toBasis (sheaf axis).degreeOneLaplacian

theorem laplacianMatrix_mulVec (axis : Fin 2) (b : Index → ℝ) :
    Matrix.mulVec (laplacianMatrix axis) b =
      ⇑((sheaf axis).degreeOneLaplacian (WithLp.toLp 2 b)) := by
  have hrepr (x : C1) :
      ⇑((EuclideanSpace.basisFun Index ℝ).toBasis.repr x) = ⇑x := by
    funext i
    simp
  simpa only [laplacianMatrix, hrepr, WithLp.ofLp_toLp]
    using LinearMap.toMatrix_mulVec_repr
      (EuclideanSpace.basisFun Index ℝ).toBasis
      (EuclideanSpace.basisFun Index ℝ).toBasis
      (sheaf axis).degreeOneLaplacian (WithLp.toLp 2 b)

@[simp] theorem laplacianMatrix_apply (axis i j : Fin 2) :
    laplacianMatrix axis ⟨(), i⟩ ⟨(), j⟩ =
      if i = axis ∧ j = axis then 1 else 0 := by
  rw [laplacianMatrix, LinearMap.toMatrix_apply]
  simp only [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  rw [degreeOneLaplacian_apply]
  by_cases hi : i = axis <;> by_cases hj : j = axis <;>
    simp_all [PiLp.single_apply, eq_comm]

theorem laplacianMatrix_eq_diagonal (axis : Fin 2) :
    laplacianMatrix axis = Matrix.diagonal
      (fun p : Index => if p.2 = axis then (1 : ℝ) else 0) := by
  ext ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩
  by_cases hij : i = j
  · subst j
    simp
  · by_cases hi : i = axis <;> by_cases hj : j = axis <;>
      simp_all

/-- Coordinate transposition of the common cochain index. -/
def coordinateSwap : Index ≃ Index where
  toFun p := ⟨p.1, other p.2⟩
  invFun p := ⟨p.1, other p.2⟩
  left_inv := by rintro ⟨⟨⟩, j⟩; fin_cases j <;> rfl
  right_inv := by rintro ⟨⟨⟩, j⟩; fin_cases j <;> rfl

/-- The private degree-one isometry exchanges the two coordinate axes. -/
def cochainSwap : C1 ≃ₗᵢ[ℝ] C1 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ coordinateSwap

@[simp] theorem cochainSwap_apply (b : C1) (j : Fin 2) :
    cochainSwap b ⟨(), j⟩ = b ⟨(), other j⟩ := rfl

@[simp] theorem cochainSwap_symm_apply (b : C1) (j : Fin 2) :
    cochainSwap.symm b ⟨(), j⟩ = b ⟨(), other j⟩ := by
  simp only [cochainSwap, LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

/-- Actual isometric chain equivalence between the two cellular presentations. -/
def axisSwap : IsometricCochainEquiv (sheaf 0) (sheaf 1) where
  degreeZero := LinearIsometryEquiv.refl ℝ _
  degreeOne := cochainSwap
  degreeTwo := LinearIsometryEquiv.refl ℝ _
  delta0_commutes := by simp
  delta1_commutes := by
    apply LinearMap.ext
    intro b
    apply PiLp.ext
    rintro ⟨⟨⟩, j⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change (sheaf 0).delta1 b ⟨(), 0⟩ =
      (sheaf 1).delta1 (cochainSwap b) ⟨(), 0⟩
    simp

theorem degreeOneLaplacian_idempotent (axis : Fin 2) (b : C1) :
    (sheaf axis).degreeOneLaplacian ((sheaf axis).degreeOneLaplacian b) =
      (sheaf axis).degreeOneLaplacian b := by
  apply PiLp.ext
  rintro ⟨⟨⟩, j⟩
  simp

theorem unitCochain_ne_zero (axis : Fin 2) : unitCochain axis ≠ 0 := by
  intro h
  have hc := congrArg (fun b : C1 => b ⟨(), axis⟩) h
  simp at hc

/-- One is an actual eigenvalue of the true cellular Hodge operator. -/
theorem hasEigenvalue_one (axis : Fin 2) :
    Module.End.HasEigenvalue (sheaf axis).degreeOneLaplacian 1 := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := unitCochain axis)
  refine ⟨?_, unitCochain_ne_zero axis⟩
  rw [Module.End.mem_eigenspace_iff]
  apply PiLp.ext
  rintro ⟨⟨⟩, j⟩
  simp

/-- The actual true Hodge operator has no eigenvalue other than zero and one. -/
theorem eigenvalue_eq_zero_or_one (axis : Fin 2) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (sheaf axis).degreeOneLaplacian μ) :
    μ = 0 ∨ μ = 1 := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have h := degreeOneLaplacian_idempotent axis v
  rw [hv.apply_eq_smul, map_smul, hv.apply_eq_smul, smul_smul] at h
  have hz : (μ * μ - μ) • v = 0 := by rw [sub_smul, h, sub_self]
  have hs : μ * μ - μ = 0 := (smul_eq_zero.mp hz).resolve_right hv.2
  have hm : μ * (μ - 1) = 0 := by nlinarith [hs]
  rcases mul_eq_zero.mp hm with hzero | hone
  · exact Or.inl hzero
  · exact Or.inr (sub_eq_zero.mp hone)

/-- The positive spectrum of the actual Hodge operator is the singleton one. -/
theorem positiveEigenvalues_eq_singleton (axis : Fin 2) :
    {μ : ℝ | 0 < μ ∧ Module.End.HasEigenvalue (sheaf axis).degreeOneLaplacian μ} =
      {1} := by
  ext μ
  constructor
  · rintro ⟨hpos, heig⟩
    rcases eigenvalue_eq_zero_or_one axis heig with hzero | hone
    · exact False.elim (hpos.ne' hzero)
    · exact hone
  · intro h
    have hμ : μ = 1 := h
    subst μ
    exact ⟨zero_lt_one, hasEigenvalue_one axis⟩

/-- The least positive eigenvalue is computed from the actual operator. -/
theorem positiveSpectralGap_eq_one (axis : Fin 2) :
    sInf {μ : ℝ | 0 < μ ∧
      Module.End.HasEigenvalue (sheaf axis).degreeOneLaplacian μ} = 1 := by
  rw [positiveEigenvalues_eq_singleton]
  simp

/-- A concrete rank-one lattice basis along the harmonic coordinate. -/
def harmonicLattice (axis : Fin 2) : CVP.ExplicitLattice Index (Fin 1) where
  basis p _ := if p.2 = other axis then 1 else 0
  basis_injective := by
    intro a b h
    have hc := congrFun h ⟨(), other axis⟩
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, ite_true, one_mul] at hc
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    simpa only [hj] using hc

theorem harmonicLatticeVector_eq (axis : Fin 2) (z : Fin 1 → ℤ) :
    WithLp.toLp 2 (CVP.latticeVector (harmonicLattice axis) z) =
      (z 0 : ℝ) • unitCochain (other axis) := by
  apply PiLp.ext
  rintro ⟨⟨⟩, j⟩
  simp [CVP.latticeVector, harmonicLattice, Matrix.mulVec, dotProduct,
    unitCochain_apply]

/-- A fully instantiated full-span integral harmonic lattice presentation. -/
def harmonicLatticePresentation (axis : Fin 2) :
    HarmonicLatticePresentation (integralStructure axis) (Fin 1) where
  lattice := harmonicLattice axis
  latticeVector_mem z := by
    rw [harmonicLatticeVector_eq]
    rw [Int.cast_smul_eq_zsmul]
    have hm : unitCochain (other axis) ∈
        (integralStructure axis).harmonicOneLattice := (message axis).2
    exact (integralStructure axis).harmonicOneLattice.zsmul_mem hm (z 0)
  realSpan_eq_harmonic := by
    apply le_antisymm
    · rintro b ⟨a, rfl⟩
      change (sheaf axis).IsHarmonicOneCochain _
      rw [harmonic_iff]
      change (∑ j : Fin 1,
        (if axis = other axis then (1 : ℝ) else 0) * a j) = 0
      simp [Ne.symm (other_ne axis)]
    · intro b hb
      have hzero : b ⟨(), axis⟩ = 0 := (harmonic_iff axis b).mp hb
      refine ⟨fun _ => b ⟨(), other axis⟩, ?_⟩
      apply PiLp.ext
      rintro ⟨⟨⟩, j⟩
      change (∑ k : Fin 1,
        (if j = other axis then (1 : ℝ) else 0) * b ⟨(), other axis⟩) = b ⟨(), j⟩
      fin_cases axis <;> fin_cases j <;>
        simp_all

/-- The constructed harmonic lattice uses the complementary unit coordinate. -/
theorem harmonicLatticePresentation_point (axis : Fin 2) (z : Fin 1 → ℤ) :
    ((harmonicLatticePresentation axis).point z).1 =
      (z 0 : ℝ) • unitCochain (other axis) := by
  change WithLp.toLp 2 (CVP.latticeVector (harmonicLattice axis) z) = _
  exact harmonicLatticeVector_eq axis z

/-- Each sample message is the unit-coefficient point of its actual lattice. -/
theorem sample_message_eq_point (axis : Fin 2) :
    (sample axis).message =
      (harmonicLatticePresentation axis).point (fun _ : Fin 1 => 1) := by
  apply Subtype.ext
  rw [harmonicLatticePresentation_point]
  simp [sample, message]

/-- The concrete sample is an instance of the existing harmonic-lattice encryptor. -/
theorem sample_eq_encrypt_one (axis : Fin 2) :
    sample axis = (harmonicLatticePresentation axis).encrypt
      (fun _ : Fin 1 => 1) (opening axis) := by
  have hm := sample_message_eq_point axis
  change message axis = _ at hm
  change ({ message := message axis, opening := opening axis } :
    HodgeEncryptedCochain (integralStructure axis)) =
      { message := (harmonicLatticePresentation axis).point (fun _ : Fin 1 => 1),
        opening := opening axis }
  rw [hm]

end Hcrypt.Sheaf.HCPAxisFamily
