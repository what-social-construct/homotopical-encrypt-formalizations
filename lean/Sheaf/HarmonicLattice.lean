module

public import Sheaf.Integral

@[expose] public section

/-!
# Harmonic-lattice messages and Hodge-structured cochains

This module connects the integral cellular-sheaf structure to the existing
degree-one Hodge decomposition.

A message lies in the intrinsic lattice `C¹_ℤ ∩ ker Δ₁`.  Its Hodge opening
provides exact and coexact noise coordinates, and the observed cochain is

`b = h + δ₀ a + δ₁* c`.

Harmonic projection recovers `h` exactly.  An optional explicit full-rank
harmonic sublattice presentation selects a concrete lattice for a CVP instance.
-/

set_option autoImplicit false

open scoped RealInnerProductSpace

noncomputable section

namespace HomotopicalEncryption
namespace Sheaf
namespace CellularSheaf

variable
  {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : OrientedTwoComplex Vertex Edge Face}

/-- Exact and coexact coordinates of Hodge-structured degree-one noise. -/
structure HodgeNoise (F : CellularSheaf X) where
  exactOpening : F.C0
  coexactOpening : F.C2

namespace HodgeNoise

variable {F : CellularSheaf X}

/-- The degree-one noise represented by exact and coexact coordinates. -/
def value (e : HodgeNoise F) : F.C1 :=
  F.delta0 e.exactOpening + F.delta1.adjoint e.coexactOpening

/-- The exact component exposed by an exact cochain commitment. -/
def exactComponent (e : HodgeNoise F) : F.C1 :=
  F.delta0 e.exactOpening

/-- The coexact component of a Hodge opening. -/
def coexactComponent (e : HodgeNoise F) : F.C1 :=
  F.delta1.adjoint e.coexactOpening

/-- Hodge-structured noise is orthogonal to every harmonic one-cochain. -/
theorem value_mem_harmonic_orthogonal (e : HodgeNoise F) :
    e.value ∈ F.harmonicOneSubspace.orthogonal := by
  rw [Submodule.mem_orthogonal']
  intro h hh
  change
    inner ℝ
      (F.delta0 e.exactOpening + F.delta1.adjoint e.coexactOpening) h = 0
  rw [inner_add_left]
  have hHarmonic : F.IsHarmonicOneCochain h :=
    LinearMap.mem_ker.mp hh
  rw [F.inner_delta0_harmonic_eq_zero e.exactOpening hHarmonic]
  have hcoexact :
      inner ℝ (F.delta1.adjoint e.coexactOpening) h = 0 := by
    rw [real_inner_comm]
    exact F.inner_harmonic_delta1Adjoint_eq_zero e.coexactOpening hHarmonic
  rw [hcoexact, add_zero]

end HodgeNoise

/--
A harmonic integral message together with exact/coexact Hodge noise.

The observed cochain is defined below as `message + noise`; it is not asserted
to be integral or exact.
-/
structure HodgeEncryptedCochain
    {F : CellularSheaf X}
    (I : IntegralStructure F) where
  message : I.harmonicOneLattice
  opening : HodgeNoise F

namespace HodgeEncryptedCochain

variable {F : CellularSheaf X}
variable {I : IntegralStructure F}

/-- The ambient degree-one cochain observed by the public layer. -/
def observed (E : HodgeEncryptedCochain I) : F.C1 :=
  E.message.1 + E.opening.value

theorem message_integral (E : HodgeEncryptedCochain I) :
    E.message.1 ∈ I.integralOneCochains :=
  I.integral_of_mem_harmonicOneLattice E.message.2

theorem message_harmonic (E : HodgeEncryptedCochain I) :
    E.message.1 ∈ F.harmonicOneSubspace :=
  I.harmonic_of_mem_harmonicOneLattice E.message.2

/-- Harmonic projection of a valid Hodge-encrypted cochain recovers its message. -/
theorem harmonicOneProjection_observed (E : HodgeEncryptedCochain I) :
    F.harmonicOneProjection E.observed = E.message.1 := by
  rw [observed, harmonicOneProjection, LinearMap.map_add]
  change
    F.harmonicOneSubspace.starProjection E.message.1 +
        F.harmonicOneSubspace.starProjection E.opening.value =
      E.message.1
  rw [F.harmonicOneSubspace.starProjection_eq_self_iff.mpr E.message_harmonic]
  rw [F.harmonicOneSubspace.starProjection_apply_eq_zero_iff.mpr
    E.opening.value_mem_harmonic_orthogonal]
  exact add_zero _

end HodgeEncryptedCochain

/--
An explicit full-rank harmonic sublattice of the intrinsic harmonic lattice.

The first proof says every integer combination lands in
`C¹_ℤ ∩ ker Δ₁`.  The span equality certifies that the lattice has full real
span in the harmonic subspace; it does not identify the discrete lattice with
that real subspace or assert that it contains every integral harmonic cochain.
-/
structure HarmonicLatticePresentation
    {F : CellularSheaf X}
    (I : IntegralStructure F)
    (Rank : Type*) [Fintype Rank] where
  lattice : CVP.ExplicitLattice (TotalCoord Edge F.edgeDim) Rank
  latticeVector_mem :
    ∀ z : Rank → ℤ,
      WithLp.toLp 2 (CVP.latticeVector lattice z) ∈ I.harmonicOneLattice
  realSpan_eq_harmonic :
    LinearMap.range
        ((WithLp.linearEquiv 2 ℝ (TotalCoord Edge F.edgeDim → ℝ)).symm.toLinearMap.comp
          (Matrix.mulVecLin lattice.basis)) =
      F.harmonicOneSubspace

namespace HarmonicLatticePresentation

variable {F : CellularSheaf X}
variable {I : IntegralStructure F}
variable {Rank : Type*} [Fintype Rank]

/-- The harmonic-lattice point represented by integer coefficients. -/
def point
    (H : HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ) :
    I.harmonicOneLattice :=
  ⟨WithLp.toLp 2 (CVP.latticeVector H.lattice z), H.latticeVector_mem z⟩

/-- Build a Hodge-encrypted cochain from explicit lattice coefficients. -/
def encrypt
    (H : HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ)
    (opening : HodgeNoise F) :
    HodgeEncryptedCochain I where
  message := H.point z
  opening := opening

/-- The known-lattice CVP instance attached to an observed Hodge cochain. -/
def cvpInstance
    (H : HarmonicLatticePresentation I Rank)
    (E : HodgeEncryptedCochain I) :
    CVP.Instance (TotalCoord Edge F.edgeDim) Rank where
  lattice := H.lattice
  target := E.observed

theorem point_mem_explicitLattice
    (H : HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ) :
    CVP.InExplicitLattice H.lattice (H.point z).1 :=
  ⟨z, rfl⟩

theorem encrypt_projection_eq_point
    (H : HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ)
    (opening : HodgeNoise F) :
    F.harmonicOneProjection (H.encrypt z opening).observed =
      (H.point z).1 :=
  (H.encrypt z opening).harmonicOneProjection_observed

/-- CVP's coordinate distance agrees with the squared Euclidean norm. -/
theorem squaredEuclideanDistance_eq_norm_sq
    {Index : Type*} [Fintype Index]
    (u v : EuclideanSpace ℝ Index) :
    CVP.squaredEuclideanDistance u v = ‖u - v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [CVP.squaredEuclideanDistance, Real.norm_eq_abs, sq_abs]

/--
For an observed Hodge cochain and a harmonic lattice point `v`,
`d²(b,v) = d²(b,h) + d²(h,v)`.
-/
theorem squaredDistance_observed_decomposition
    (H : HarmonicLatticePresentation I Rank)
    (E : HodgeEncryptedCochain I)
    (v : CVP.AmbientVector (TotalCoord Edge F.edgeDim))
    (hv : CVP.InExplicitLattice H.lattice v) :
    CVP.squaredEuclideanDistance E.observed v =
      CVP.squaredEuclideanDistance E.observed E.message.1 +
        CVP.squaredEuclideanDistance E.message.1 v := by
  rcases hv with ⟨w, rfl⟩
  let v : F.C1 := WithLp.toLp 2 (CVP.latticeVector H.lattice w)
  change CVP.squaredEuclideanDistance E.observed v =
    CVP.squaredEuclideanDistance E.observed E.message.1 +
      CVP.squaredEuclideanDistance E.message.1 v
  rw [squaredEuclideanDistance_eq_norm_sq,
    squaredEuclideanDistance_eq_norm_sq,
    squaredEuclideanDistance_eq_norm_sq]
  let h : F.C1 := E.message.1
  let e : F.C1 := E.opening.value
  change ‖h + e - v‖ ^ 2 = ‖h + e - h‖ ^ 2 + ‖h - v‖ ^ 2
  have hvHarmonic : v ∈ F.harmonicOneSubspace :=
    I.harmonic_of_mem_harmonicOneLattice (H.latticeVector_mem w)
  have hdiff : h - v ∈ F.harmonicOneSubspace :=
    F.harmonicOneSubspace.sub_mem E.message_harmonic hvHarmonic
  have hopen := E.opening.value_mem_harmonic_orthogonal
  rw [Submodule.mem_orthogonal'] at hopen
  have horth : inner ℝ e (h - v) = 0 :=
    hopen (h - v) hdiff
  have hpyth :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero e (h - v) horth
  have hleft : h + e - v = e + (h - v) := by
    abel
  have hnoise : h + e - h = e := by
    abel
  rw [hleft, hnoise]
  simpa [pow_two] using hpyth

/-- The encoded harmonic lattice point is a closest vector to its observation. -/
theorem point_isClosest_observed
    (H : HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ)
    (opening : HodgeNoise F) :
    CVP.IsClosestLatticeVector H.lattice
      (H.encrypt z opening).observed (H.point z).1 := by
  refine ⟨H.point_mem_explicitLattice z, ?_⟩
  intro v hv
  have hvd :=
    H.squaredDistance_observed_decomposition (H.encrypt z opening) v hv
  have hhd :=
    H.squaredDistance_observed_decomposition (H.encrypt z opening)
      (H.point z).1 (H.point_mem_explicitLattice z)
  rw [hhd, hvd]
  change
    CVP.squaredEuclideanDistance (H.encrypt z opening).observed (H.point z).1 +
        CVP.squaredEuclideanDistance (H.point z).1 (H.point z).1 ≤
      CVP.squaredEuclideanDistance (H.encrypt z opening).observed (H.point z).1 +
        CVP.squaredEuclideanDistance (H.point z).1 v
  have hzero :
      CVP.squaredEuclideanDistance (H.point z).1 (H.point z).1 = 0 := by
    simp [CVP.squaredEuclideanDistance]
  rw [hzero, add_zero]
  exact le_add_of_nonneg_right
    (CVP.squaredEuclideanDistance_nonneg (H.point z).1 v)

/-- A valid encoded sample has the encoded point as its unique closest vector. -/
theorem isClosest_observed_iff_eq_point
    (H : HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ)
    (opening : HodgeNoise F)
    (v : CVP.AmbientVector (TotalCoord Edge F.edgeDim)) :
    CVP.IsClosestLatticeVector H.lattice
        (H.encrypt z opening).observed v ↔
      v = (H.point z).1 := by
  constructor
  · intro hv
    have hle :=
      hv.2 (H.point z).1 (H.point_mem_explicitLattice z)
    have hvd :=
      H.squaredDistance_observed_decomposition
        (H.encrypt z opening) v hv.1
    have hhd :=
      H.squaredDistance_observed_decomposition
        (H.encrypt z opening) (H.point z).1
        (H.point_mem_explicitLattice z)
    rw [hvd, hhd] at hle
    change
      CVP.squaredEuclideanDistance (H.encrypt z opening).observed (H.point z).1 +
          CVP.squaredEuclideanDistance (H.point z).1 v ≤
        CVP.squaredEuclideanDistance (H.encrypt z opening).observed (H.point z).1 +
          CVP.squaredEuclideanDistance (H.point z).1 (H.point z).1 at hle
    have hzero :
        CVP.squaredEuclideanDistance (H.point z).1 (H.point z).1 = 0 := by
      simp [CVP.squaredEuclideanDistance]
    rw [hzero, add_zero] at hle
    have hdist_le :
        CVP.squaredEuclideanDistance (H.point z).1 v ≤ 0 := by
      linarith
    have hdist_nonneg :
        0 ≤ CVP.squaredEuclideanDistance (H.point z).1 v :=
      CVP.squaredEuclideanDistance_nonneg (H.point z).1 v
    have hdist :
        CVP.squaredEuclideanDistance (H.point z).1 v = 0 :=
      le_antisymm hdist_le hdist_nonneg
    let vE : F.C1 := WithLp.toLp 2 v
    have hdistE :
        CVP.squaredEuclideanDistance (H.point z).1 vE = 0 := by
      exact hdist
    rw [squaredEuclideanDistance_eq_norm_sq] at hdistE
    have hnorm : ‖(H.point z).1 - vE‖ = 0 :=
      sq_eq_zero_iff.mp hdistE
    have hsub : (H.point z).1 - vE = 0 :=
      norm_eq_zero.mp hnorm
    have heq : (H.point z).1 = vE :=
      sub_eq_zero.mp hsub
    funext i
    exact (congrArg (fun b : F.C1 => b i) heq).symm
  · rintro rfl
    exact H.point_isClosest_observed z opening

/-- Instance-level unique-solution form of the concrete Hodge/CVP bridge. -/
theorem solution_cvpInstance_iff_eq_point
    (H : HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ)
    (opening : HodgeNoise F)
    (v : CVP.AmbientVector (TotalCoord Edge F.edgeDim)) :
    CVP.Solution (H.cvpInstance (H.encrypt z opening)) v ↔
      v = (H.point z).1 :=
  H.isClosest_observed_iff_eq_point z opening v

theorem existsUnique_solution_cvpInstance
    (H : HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ)
    (opening : HodgeNoise F) :
    ∃! v, CVP.Solution (H.cvpInstance (H.encrypt z opening)) v := by
  refine ⟨(H.point z).1, ?_, ?_⟩
  · exact H.point_isClosest_observed z opening
  · intro v hv
    exact (H.solution_cvpInstance_iff_eq_point z opening v).mp hv

end HarmonicLatticePresentation

end CellularSheaf
end Sheaf
end HomotopicalEncryption
