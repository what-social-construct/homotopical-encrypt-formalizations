module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic
public import Hardness
public import HCP.AxisFamily
public import Sheaf.CoefficientRecovery

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
open scoped BigOperators RealInnerProductSpace

/-!
# Proofs for the Paper 1 statement surface

The statement vocabulary matches Challenge. All owner adapters below retain
existing incidences, lattice bases, operators, samples and public theories.
Proofs reuse the canonical development; no statement imports Challenge.
-/

namespace HomotopicalEncryption.Palomar.PaperOne
noncomputable section
open scoped BigOperators

/-- Harmonicity in the displayed finite coordinate matrix. -/
def MatrixIsHarmonic {N : Type} [Fintype N] {R : Type} [CommRing R]
    (Δ : Matrix N N R) (h : N → R) : Prop := Δ.mulVec h = 0

namespace CVP
/-- Real ambient coordinates, retaining the finite coordinate index. -/
abbrev AmbientVector (m : Type*) := m → ℝ
/-- A real full-column-rank basis; its integer combinations form the lattice. -/
structure ExplicitLattice (m n : Type*) [Fintype n] where
  basis : Matrix m n ℝ
  basis_injective : Function.Injective (Matrix.mulVec basis)
/-- The actual integer-generated lattice point. -/
def latticeVector {m n : Type*} [Fintype n]
    (L : ExplicitLattice m n) (z : n → ℤ) : AmbientVector m :=
  L.basis.mulVec fun j => (z j : ℝ)
/-- Membership in the discrete lattice, not its real span. -/
def InExplicitLattice {m n : Type*} [Fintype n]
    (L : ExplicitLattice m n) (v : AmbientVector m) : Prop :=
  ∃ z : n → ℤ, latticeVector L z = v
/-- Squared Euclidean distance has the ordinary Euclidean minimizers. -/
def squaredEuclideanDistance {m : Type*} [Fintype m] (u v : AmbientVector m) : ℝ :=
  ∑ i, (u i - v i) ^ 2
/-- A known lattice and an ambient target. -/
structure Instance (m n : Type*) [Fintype n] where
  lattice : ExplicitLattice m n
  target : AmbientVector m
/-- An exact discrete closest-vector answer. -/
def IsClosestLatticeVector {m n : Type*} [Fintype m] [Fintype n]
    (L : ExplicitLattice m n) (t v : AmbientVector m) : Prop :=
  InExplicitLattice L v ∧ ∀ w, InExplicitLattice L w →
    squaredEuclideanDistance t v ≤ squaredEuclideanDistance t w
/-- Instance-oriented exact CVP. -/
def Solution {m n : Type*} [Fintype m] [Fintype n]
    (I : Instance m n) (v : AmbientVector m) : Prop :=
  IsClosestLatticeVector I.lattice I.target v
/-- Oracle input includes the explicit basis and target. -/
def Oracle (m n : Type*) [Fintype m] [Fintype n] :=
  ExplicitLattice m n → AmbientVector m → AmbientVector m
/-- Correctness for every presented lattice and target. -/
def OracleCorrect {m n : Type*} [Fintype m] [Fintype n] (O : Oracle m n) : Prop :=
  ∀ L t, IsClosestLatticeVector L t (O L t)
/-- Coordinates of orthogonal projection onto the supplied harmonic space. -/
def projectedTarget {m : Type} [Fintype m]
    (W : Submodule ℝ (EuclideanSpace ℝ m)) [W.HasOrthogonalProjection]
    (t : AmbientVector m) : AmbientVector m :=
  fun i => W.starProjection (WithLp.toLp 2 t) i
end CVP
end
end HomotopicalEncryption.Palomar.PaperOne

namespace HomotopicalEncryption.Palomar.PaperOne

open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- Finite oriented incidences with the actual cellular boundary equation. -/
structure OrientedTwoComplex (Vertex Edge Face : Type*)
    [Fintype Vertex] [Fintype Edge] [Fintype Face] where
  incidence01 : Vertex → Edge → ℤ
  incidence12 : Edge → Face → ℤ
  boundarySqZero : ∀ v f,
    (Finset.univ : Finset Edge).sum (fun e => incidence01 v e * incidence12 e f) = 0

namespace OrientedTwoComplex
variable {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  (X : OrientedTwoComplex Vertex Edge Face)
/-- A vertex-edge flag is incident exactly when its integer incidence is nonzero. -/
def VertexEdgeIncident (v : Vertex) (e : Edge) : Prop := X.incidence01 v e ≠ 0
/-- An edge-face flag is incident exactly when its integer incidence is nonzero. -/
def EdgeFaceIncident (e : Edge) (f : Face) : Prop := X.incidence12 e f ≠ 0
/-- The vertex-edge incidence coefficient extended from integers to real scalars. -/
def incidence01Real (v : Vertex) (e : Edge) : ℝ := X.incidence01 v e
/-- The edge-face incidence coefficient extended from integers to real scalars. -/
def incidence12Real (e : Edge) (f : Face) : ℝ := X.incidence12 e f
end OrientedTwoComplex

/-- A real Euclidean stalk with its standard inner product and n coordinates. -/
abbrev Coord (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Stalk maps compose on each incident flag; coboundaries are defined below. -/
structure CellularSheaf {Vertex Edge Face : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face]
    (X : OrientedTwoComplex Vertex Edge Face) where
  vertexDim : Vertex → ℕ
  edgeDim : Edge → ℕ
  faceDim : Face → ℕ
  restrict01 : ∀ v e, Coord (vertexDim v) →ₗ[ℝ] Coord (edgeDim e)
  restrict12 : ∀ e f, Coord (edgeDim e) →ₗ[ℝ] Coord (faceDim f)
  restrict02 : ∀ v f, Coord (vertexDim v) →ₗ[ℝ] Coord (faceDim f)
  restrictionComp : ∀ v e f, X.VertexEdgeIncident v e → X.EdgeFaceIncident e f →
    (restrict12 e f).comp (restrict01 v e) = restrict02 v f

namespace CellularSheaf
variable {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : OrientedTwoComplex Vertex Edge Face}

/-- The coordinate index consisting of a cell and a coordinate in its stalk. -/
abbrev TotalCoord (Cell : Type*) (dim : Cell → ℕ) := Σ c : Cell, Fin (dim c)
/-- The finite Euclidean direct sum of the cell stalks. -/
abbrev Cochain (Cell : Type*) [Fintype Cell] (dim : Cell → ℕ) :=
  EuclideanSpace ℝ (TotalCoord Cell dim)
/-- Degree-zero cochains on the vertex stalks. -/
abbrev C0 (F : CellularSheaf X) := Cochain Vertex F.vertexDim
/-- Degree-one cochains on the edge stalks. -/
abbrev C1 (F : CellularSheaf X) := Cochain Edge F.edgeDim
/-- Degree-two cochains on the face stalks. -/
abbrev C2 (F : CellularSheaf X) := Cochain Face F.faceDim

/-- The linear projection of a cochain to the stalk at the selected cell. -/
def component {Cell : Type*} [Fintype Cell] (dim : Cell → ℕ) (c : Cell) :
    Cochain Cell dim →ₗ[ℝ] Coord (dim c) where
  toFun x := WithLp.toLp 2 (fun i => x ⟨c, i⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The linear cochain map assembled from one stalk-valued map per cell. -/
def assemble {Cell A : Type*} [Fintype Cell] [AddCommMonoid A] [Module ℝ A]
    (dim : Cell → ℕ) (L : ∀ c, A →ₗ[ℝ] Coord (dim c)) :
    A →ₗ[ℝ] Cochain Cell dim where
  toFun x := WithLp.toLp 2 (fun p : TotalCoord Cell dim => L p.1 x p.2)
  map_add' x y := by
    apply PiLp.ext
    intro p
    exact congrArg (fun z : Coord (dim p.1) => z p.2) ((L p.1).map_add x y)
  map_smul' a x := by
    apply PiLp.ext
    intro p
    exact congrArg (fun z : Coord (dim p.1) => z p.2) ((L p.1).map_smul a x)

/-- The edge block of the incidence-weighted vertex-to-edge coboundary. -/
def delta0At (F : CellularSheaf X) (e : Edge) : F.C0 →ₗ[ℝ] Coord (F.edgeDim e) :=
  (Finset.univ : Finset Vertex).sum fun v =>
    X.incidence01Real v e • (F.restrict01 v e).comp (component F.vertexDim v)
/-- The face block of the incidence-weighted edge-to-face coboundary. -/
def delta1At (F : CellularSheaf X) (f : Face) : F.C1 →ₗ[ℝ] Coord (F.faceDim f) :=
  (Finset.univ : Finset Edge).sum fun e =>
    X.incidence12Real e f • (F.restrict12 e f).comp (component F.edgeDim e)
/-- The actual cellular coboundary from degree zero to degree one. -/
def delta0 (F : CellularSheaf X) : F.C0 →ₗ[ℝ] F.C1 := assemble F.edgeDim (delta0At F)
/-- The actual cellular coboundary from degree one to degree two. -/
def delta1 (F : CellularSheaf X) : F.C1 →ₗ[ℝ] F.C2 := assemble F.faceDim (delta1At F)

/-- The true degree-one Hodge operator, rather than its kernel normalization. -/
def degreeOneLaplacian (F : CellularSheaf X) : F.C1 →ₗ[ℝ] F.C1 :=
  F.delta0.comp F.delta0.adjoint + F.delta1.adjoint.comp F.delta1
/-- A degree-one cochain is harmonic when the true Hodge Laplacian annihilates it. -/
def IsHarmonicOneCochain (F : CellularSheaf X) (b : F.C1) : Prop :=
  F.degreeOneLaplacian b = 0
/-- The real kernel of the degree-one Hodge Laplacian. -/
def harmonicOneSubspace (F : CellularSheaf X) : Submodule ℝ F.C1 :=
  LinearMap.ker F.degreeOneLaplacian
/-- The orthogonal projection onto the harmonic degree-one subspace. -/
def harmonicOneProjection (F : CellularSheaf X) : F.C1 →ₗ[ℝ] F.C1 :=
  F.harmonicOneSubspace.starProjection.toLinearMap

/-- Full-rank integral coordinates on one stalk. -/
structure StalkLattice (n : ℕ) where
  presentation : CVP.ExplicitLattice (Fin n) (Fin n)
namespace StalkLattice
/-- The additive subgroup of integer combinations of the chosen stalk basis. -/
def carrier {n : ℕ} (L : StalkLattice n) : AddSubgroup (Coord n) where
  carrier := {x | CVP.InExplicitLattice L.presentation x}
  zero_mem' := by
    refine ⟨0, ?_⟩
    funext i
    simp only [CVP.latticeVector, Matrix.mulVec, dotProduct, Pi.zero_apply,
      Int.cast_zero, mul_zero, Finset.sum_const_zero, WithLp.ofLp_zero]
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    funext i
    change (∑ j, L.presentation.basis i j * ((a j + b j : ℤ) : ℝ)) = x i + y i
    rw [← congrFun ha i, ← congrFun hb i]
    simp only [CVP.latticeVector, Matrix.mulVec, dotProduct,
      Int.cast_add, mul_add, Finset.sum_add_distrib]
  neg_mem' := by
    rintro x ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    funext i
    change (∑ j, L.presentation.basis i j * ((-a j : ℤ) : ℝ)) = -x i
    rw [← congrFun ha i]
    simp only [CVP.latticeVector, Matrix.mulVec, dotProduct,
      Int.cast_neg, mul_neg, Finset.sum_neg_distrib]
/-- Membership of a real stalk vector in the chosen integral stalk lattice. -/
def Contains {n : ℕ} (L : StalkLattice n) (x : Coord n) : Prop := x ∈ L.carrier
/-- A linear stalk map sends every vector of the source lattice into the target lattice. -/
def Preserves {m n : ℕ} (L : StalkLattice m) (M : StalkLattice n)
    (f : Coord m →ₗ[ℝ] Coord n) : Prop :=
  AddSubgroup.map f.toAddMonoidHom L.carrier ≤ M.carrier
end StalkLattice

/-- The original sheaf is equipped with restriction-compatible stalk lattices. -/
structure IntegralStructure (F : CellularSheaf X) where
  vertexStalk : ∀ v, StalkLattice (F.vertexDim v)
  edgeStalk : ∀ e, StalkLattice (F.edgeDim e)
  faceStalk : ∀ f, StalkLattice (F.faceDim f)
  restrict01_preserves : ∀ v e, (vertexStalk v).Preserves (edgeStalk e) (F.restrict01 v e)
  restrict12_preserves : ∀ e f, (edgeStalk e).Preserves (faceStalk f) (F.restrict12 e f)
  restrict02_preserves : ∀ v f, (vertexStalk v).Preserves (faceStalk f) (F.restrict02 v f)
namespace IntegralStructure
variable {F : CellularSheaf X}
/-- The additive subgroup of cochains integral in every selected edge-stalk lattice. -/
def integralOneCochains (I : IntegralStructure F) : AddSubgroup F.C1 where
  carrier := {b | ∀ e, component F.edgeDim e b ∈ (I.edgeStalk e).carrier}
  zero_mem' := by
    intro e
    change (0 : Coord (F.edgeDim e)) ∈ (I.edgeStalk e).carrier
    exact (I.edgeStalk e).carrier.zero_mem
  add_mem' := by
    intro a b ha hb e
    exact (I.edgeStalk e).carrier.add_mem (ha e) (hb e)
  neg_mem' := by
    intro a ha e
    exact (I.edgeStalk e).carrier.neg_mem (ha e)
/-- The intrinsic intersection of integral degree-one cochains and the harmonic subspace. -/
def harmonicOneLattice (I : IntegralStructure F) : AddSubgroup F.C1 :=
  I.integralOneCochains ⊓ F.harmonicOneSubspace.toAddSubgroup
end IntegralStructure

/-- Exact and coexact noise openings use the actual cellular operators. -/
structure HodgeNoise (F : CellularSheaf X) where
  exactOpening : F.C0
  coexactOpening : F.C2
namespace HodgeNoise
variable {F : CellularSheaf X}
/-- The sum of the exact and coexact cellular noise components. -/
def value (e : HodgeNoise F) : F.C1 :=
  F.delta0 e.exactOpening + F.delta1.adjoint e.coexactOpening
/-- The exact noise obtained by applying the degree-zero coboundary to its opening. -/
def exactComponent (e : HodgeNoise F) : F.C1 := F.delta0 e.exactOpening
/-- The coexact noise obtained by applying the degree-one adjoint to its opening. -/
def coexactComponent (e : HodgeNoise F) : F.C1 := F.delta1.adjoint e.coexactOpening
end HodgeNoise

/-- An integral harmonic message together with exact and coexact real noise openings. -/
structure HodgeEncryptedCochain {F : CellularSheaf X} (I : IntegralStructure F) where
  message : I.harmonicOneLattice
  opening : HodgeNoise F
namespace HodgeEncryptedCochain
variable {F : CellularSheaf X} {I : IntegralStructure F}
/-- The public ambient cochain formed by adding the harmonic message and its Hodge noise. -/
def observed (E : HodgeEncryptedCochain I) : F.C1 := E.message.1 + E.opening.value
end HodgeEncryptedCochain

/-- A supplied full-span sublattice of the intrinsic integral harmonic lattice. -/
structure HarmonicLatticePresentation {F : CellularSheaf X}
    (I : IntegralStructure F) (Rank : Type*) [Fintype Rank] where
  lattice : CVP.ExplicitLattice (TotalCoord Edge F.edgeDim) Rank
  latticeVector_mem : ∀ z : Rank → ℤ,
    WithLp.toLp 2 (CVP.latticeVector lattice z) ∈ I.harmonicOneLattice
  realSpan_eq_harmonic : LinearMap.range
    ((WithLp.linearEquiv 2 ℝ (TotalCoord Edge F.edgeDim → ℝ)).symm.toLinearMap.comp
      (Matrix.mulVecLin lattice.basis)) = F.harmonicOneSubspace
namespace HarmonicLatticePresentation
variable {F : CellularSheaf X} {I : IntegralStructure F} {Rank : Type*} [Fintype Rank]
/-- The intrinsic integral harmonic point represented by the supplied integer coefficients. -/
def point (H : HarmonicLatticePresentation I Rank) (z : Rank → ℤ) :
    I.harmonicOneLattice :=
  ⟨WithLp.toLp 2 (CVP.latticeVector H.lattice z), H.latticeVector_mem z⟩
/-- The Hodge sample formed from a presented harmonic point and the supplied noise opening. -/
def encrypt (H : HarmonicLatticePresentation I Rank) (z : Rank → ℤ)
    (opening : HodgeNoise F) : HodgeEncryptedCochain I where
  message := H.point z
  opening := opening
/-- The discrete CVP instance with the supplied harmonic lattice and the observed target. -/
def cvpInstance (H : HarmonicLatticePresentation I Rank) (E : HodgeEncryptedCochain I) :
    CVP.Instance (TotalCoord Edge F.edgeDim) Rank where
  lattice := H.lattice
  target := E.observed
/-- Choice-based private decoding in this presentation; no efficiency is claimed. -/
def decodeCoefficients (H : HarmonicLatticePresentation I Rank) (b : F.C1) :
    Option (Rank → ℤ) := by
  classical
  exact if h : ∃ z : Rank → ℤ, F.harmonicOneProjection b = (H.point z).1 then
    some h.choose else none
end HarmonicLatticePresentation

end CellularSheaf
end
end HomotopicalEncryption.Palomar.PaperOne

namespace HomotopicalEncryption.Palomar.PaperOne
noncomputable section
namespace CVP.ExplicitLattice
/-- Identity on the original full-rank basis, with the same injectivity proof. -/
def toOwner {m n : Type*} [Fintype n] (L : CVP.ExplicitLattice m n) :
    _root_.CVP.ExplicitLattice m n := ⟨L.basis, L.basis_injective⟩
end CVP.ExplicitLattice

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
  exact _root_.Hodge_Decomposition_Theorem d_prev d_next h_complex

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
  exact _root_.Hodge_Decomposition_unique d_prev d_next h_complex hb hh he1 he2 hb' hh' he1' he2'

lemma exists_matrix_ker_eq_range {n : Type} [Fintype n] [DecidableEq n] {R : Type} [Field R] [DecidableEq R] (B : Matrix n n R) :
  ∃ (Δ : Matrix n n R), ∀ v, Matrix.mulVec Δ v = 0 ↔ ∃ x, Matrix.mulVec B x = v := by
  exact _root_.exists_matrix_ker_eq_range B

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
  exact _root_.Hodge_GeneratedSubspace_Reduction_Proof solver h_solver

/-- The perpendicular error is constant across every point of the supplied lattice. -/
theorem squaredDistance_projection_decomposition
    {m n : Type} [Fintype m] [Fintype n]
    (L : CVP.ExplicitLattice m n) (W : Submodule ℝ (EuclideanSpace ℝ m))
    [W.HasOrthogonalProjection]
    (hL : ∀ z : n → ℤ, WithLp.toLp 2 (CVP.latticeVector L z) ∈ W)
    (t v : CVP.AmbientVector m) (hv : CVP.InExplicitLattice L v) :
    CVP.squaredEuclideanDistance t v =
      CVP.squaredEuclideanDistance t (CVP.projectedTarget W t) +
      CVP.squaredEuclideanDistance (CVP.projectedTarget W t) v := by
  let H : _root_.HarmonicCVPBridge m n := ⟨L.toOwner, W, hL⟩
  exact H.squaredDistance_projection_decomposition t v hv

/-- Projecting a target preserves the discrete CVP solution set; the lattice is retained. -/
theorem solution_iff_projectedTarget
    {m n : Type} [Fintype m] [Fintype n]
    (L : CVP.ExplicitLattice m n) (W : Submodule ℝ (EuclideanSpace ℝ m))
    [W.HasOrthogonalProjection]
    (hL : ∀ z : n → ℤ, WithLp.toLp 2 (CVP.latticeVector L z) ∈ W)
    (t v : CVP.AmbientVector m) :
    CVP.IsClosestLatticeVector L t v ↔
      CVP.IsClosestLatticeVector L (CVP.projectedTarget W t) v := by
  let H : _root_.HarmonicCVPBridge m n := ⟨L.toOwner, W, hL⟩
  exact H.solution_iff_projectedTarget t v
end
end HomotopicalEncryption.Palomar.PaperOne

namespace HomotopicalEncryption.Palomar.PaperOne

noncomputable section

namespace OrientedTwoComplex
variable {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
def toOwner (X : OrientedTwoComplex Vertex Edge Face) :
    _root_.HomotopicalEncryption.Sheaf.OrientedTwoComplex Vertex Edge Face where
  incidence01 := X.incidence01
  incidence12 := X.incidence12
  boundarySqZero := X.boundarySqZero
end OrientedTwoComplex

namespace CellularSheaf
variable {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : OrientedTwoComplex Vertex Edge Face}

def toOwner (F : CellularSheaf X) : _root_.HomotopicalEncryption.Sheaf.CellularSheaf X.toOwner where
  vertexDim := F.vertexDim
  edgeDim := F.edgeDim
  faceDim := F.faceDim
  restrict01 := F.restrict01
  restrict12 := F.restrict12
  restrict02 := F.restrict02
  restrictionComp := F.restrictionComp

theorem delta0_toOwner (F : CellularSheaf X) : F.toOwner.delta0 = F.delta0 := rfl
theorem delta1_toOwner (F : CellularSheaf X) : F.toOwner.delta1 = F.delta1 := rfl
theorem degreeOneLaplacian_toOwner (F : CellularSheaf X) :
    F.toOwner.degreeOneLaplacian = F.degreeOneLaplacian := rfl
theorem harmonicOneSubspace_toOwner (F : CellularSheaf X) :
    F.toOwner.harmonicOneSubspace = F.harmonicOneSubspace := rfl
theorem harmonicOneProjection_toOwner (F : CellularSheaf X) :
    F.toOwner.harmonicOneProjection = F.harmonicOneProjection := rfl

/-- Cellular square-zero follows from incidences and restriction composition. -/
theorem delta1_comp_delta0 (F : CellularSheaf X) : F.delta1.comp F.delta0 = 0 := by
  exact F.toOwner.delta1_comp_delta0

namespace StalkLattice
def toOwner {n : ℕ} (L : StalkLattice n) :
    _root_.HomotopicalEncryption.Sheaf.CellularSheaf.StalkLattice n where
  presentation := L.presentation.toOwner
theorem carrier_toOwner {n : ℕ} (L : StalkLattice n) :
    L.toOwner.carrier = L.carrier := rfl
end StalkLattice

namespace IntegralStructure
variable {F : CellularSheaf X}
def toOwner (I : IntegralStructure F) :
    _root_.HomotopicalEncryption.Sheaf.CellularSheaf.IntegralStructure F.toOwner where
  vertexStalk v := (I.vertexStalk v).toOwner
  edgeStalk e := (I.edgeStalk e).toOwner
  faceStalk f := (I.faceStalk f).toOwner
  restrict01_preserves := I.restrict01_preserves
  restrict12_preserves := I.restrict12_preserves
  restrict02_preserves := I.restrict02_preserves
theorem integralOneCochains_toOwner (I : IntegralStructure F) :
    I.toOwner.integralOneCochains = I.integralOneCochains := rfl
theorem harmonicOneLattice_toOwner (I : IntegralStructure F) :
    I.toOwner.harmonicOneLattice = I.harmonicOneLattice := rfl
end IntegralStructure

namespace HodgeNoise
variable {F : CellularSheaf X}
def toOwner (e : HodgeNoise F) : _root_.HomotopicalEncryption.Sheaf.CellularSheaf.HodgeNoise F.toOwner where
  exactOpening := e.exactOpening
  coexactOpening := e.coexactOpening
theorem value_toOwner (e : HodgeNoise F) : e.toOwner.value = e.value := rfl
theorem exactComponent_toOwner (e : HodgeNoise F) :
    e.toOwner.exactComponent = e.exactComponent := rfl
theorem coexactComponent_toOwner (e : HodgeNoise F) :
    e.toOwner.coexactComponent = e.coexactComponent := rfl
end HodgeNoise

namespace HodgeEncryptedCochain
variable {F : CellularSheaf X} {I : IntegralStructure F}
def toOwner (E : HodgeEncryptedCochain I) :
    _root_.HomotopicalEncryption.Sheaf.CellularSheaf.HodgeEncryptedCochain I.toOwner where
  message := ⟨E.message.1, E.message.2⟩
  opening := E.opening.toOwner
theorem observed_toOwner (E : HodgeEncryptedCochain I) :
    E.toOwner.observed = E.observed := rfl

/-- The private harmonic projection recovers the actual sample's message. -/
theorem harmonicOneProjection_observed (E : HodgeEncryptedCochain I) :
    F.harmonicOneProjection E.observed = E.message.1 := by
  exact E.toOwner.harmonicOneProjection_observed
end HodgeEncryptedCochain

namespace HarmonicLatticePresentation
variable {F : CellularSheaf X} {I : IntegralStructure F} {Rank : Type*} [Fintype Rank]
def toOwner (H : HarmonicLatticePresentation I Rank) :
    _root_.HomotopicalEncryption.Sheaf.CellularSheaf.HarmonicLatticePresentation I.toOwner Rank where
  lattice := H.lattice.toOwner
  latticeVector_mem := H.latticeVector_mem
  realSpan_eq_harmonic := H.realSpan_eq_harmonic
theorem point_toOwner (H : HarmonicLatticePresentation I Rank) (z : Rank → ℤ) :
    (H.toOwner.point z).1 = (H.point z).1 := rfl
theorem encrypt_toOwner (H : HarmonicLatticePresentation I Rank) (z : Rank → ℤ)
    (opening : HodgeNoise F) :
    (H.encrypt z opening).toOwner = H.toOwner.encrypt z opening.toOwner := rfl
theorem cvpSolution_toOwner (H : HarmonicLatticePresentation I Rank)
    (E : HodgeEncryptedCochain I) (v : CVP.AmbientVector (TotalCoord Edge F.edgeDim)) :
    _root_.CVP.Solution (H.toOwner.cvpInstance E.toOwner) v ↔
      CVP.Solution (H.cvpInstance E) v := Iff.rfl
theorem decodeCoefficients_toOwner (H : HarmonicLatticePresentation I Rank) (b : F.C1) :
    H.toOwner.decodeCoefficients b = H.decodeCoefficients b := rfl

/-- The original integer coefficients are recovered in the supplied presentation. -/
theorem decodeCoefficients_encrypt (H : HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ) (opening : HodgeNoise F) :
    H.decodeCoefficients (H.encrypt z opening).observed = some z := by
  exact H.toOwner.decodeCoefficients_encrypt z opening.toOwner
end HarmonicLatticePresentation
end CellularSheaf

/-- The actual cellular sample's discrete CVP solutions are exactly its message. -/
theorem concreteSheafHCP_CVP_solution_iff_message
    {Vertex Edge Face Rank : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face] [Fintype Rank]
    {X : OrientedTwoComplex Vertex Edge Face} {F : CellularSheaf X}
    {I : CellularSheaf.IntegralStructure F}
    (H : CellularSheaf.HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ) (opening : CellularSheaf.HodgeNoise F)
    (v : CVP.AmbientVector (CellularSheaf.TotalCoord Edge F.edgeDim)) :
    CVP.Solution (H.cvpInstance (H.encrypt z opening)) v ↔ v = (H.point z).1 := by
  exact _root_.concreteSheafHCP_CVP_solution_iff_message H.toOwner z opening.toOwner v

/-- Each constructed cellular sample has a unique discrete CVP solution. -/
theorem concreteSheafHCP_CVP_existsUnique
    {Vertex Edge Face Rank : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face] [Fintype Rank]
    {X : OrientedTwoComplex Vertex Edge Face} {F : CellularSheaf X}
    {I : CellularSheaf.IntegralStructure F}
    (H : CellularSheaf.HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ) (opening : CellularSheaf.HodgeNoise F) :
    ∃! v, CVP.Solution (H.cvpInstance (H.encrypt z opening)) v := by
  exact _root_.concreteSheafHCP_CVP_existsUnique H.toOwner z opening.toOwner

end
end HomotopicalEncryption.Palomar.PaperOne


namespace HomotopicalEncryption.Palomar.PaperOne
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ZeroObject
noncomputable section
namespace Helfer
universe u₁ u₂ v₁ v₂ w
/-- A collection of sorts and algebraic function symbols of finite arity. -/
structure Signature where
  Sorts : Type u₁
  FunctionSymbol : List Sorts → Sorts → Type v₁
variable (C : Type u₂) [Category.{v₂} C] [HasTerminal C] [HasBinaryProducts C]
/-- Objects for sorts and morphisms interpreting the algebraic function symbols. -/
structure Interpretation (S : Signature) where
  onSort : S.Sorts → C
  onFunction : ∀ {Γ : List S.Sorts} {B : S.Sorts},
    S.FunctionSymbol Γ B → (_root_.HomotopicalEncryption.Helfer.contextObject C onSort Γ ⟶ onSort B)
variable {C} [ModelCategory C] {S : Signature.{u₁, v₁}}
/-- Sortwise morphisms preserving function symbols up to right homotopy. -/
structure HomotopyHomomorphism (M N : Interpretation C S) where
  component : ∀ A, M.onSort A ⟶ N.onSort A
  preservesFunction : ∀ {Γ : List S.Sorts} {B : S.Sorts} (f : S.FunctionSymbol Γ B),
    RightHomotopyRel (M.onFunction f ≫ component B)
      (_root_.HomotopicalEncryption.Helfer.contextMap C component Γ ≫ N.onFunction f)
/-- A sortwise weak equivalence whose source and target sort objects are cofibrant and fibrant. -/
structure HomotopyEquivalence (M N : Interpretation C S) extends HomotopyHomomorphism M N where
  sourceFibrant : ∀ A, IsFibrant (M.onSort A)
  targetFibrant : ∀ A, IsFibrant (N.onSort A)
  sourceCofibrant : ∀ A, IsCofibrant (M.onSort A)
  targetCofibrant : ∀ A, IsCofibrant (N.onSort A)
  componentWeakEquivalence : ∀ A, WeakEquivalence (toHomotopyHomomorphism.component A)
/-- Existence of a typed homotopy equivalence between two interpretations. -/
def HomotopyEquivalent (M N : Interpretation C S) : Prop := Nonempty (HomotopyEquivalence M N)
/-- A specified collection of closed tests and a satisfaction predicate. -/
structure ClosedSemantics (S : Signature.{u₁, v₁}) where
  ClosedFormula : Type w
  Satisfies : Interpretation C S → ClosedFormula → Prop
/-- The set of specified closed tests satisfied by an interpretation. -/
def ClosedTheory (sem : ClosedSemantics (C := C) S) (M : Interpretation C S) :
    Set sem.ClosedFormula := {φ | sem.Satisfies M φ}
/-- The explicit hypothesis that the specified closed tests are invariant under typed homotopy equivalence. -/
structure ClosedFormulaInvariance (sem : ClosedSemantics (C := C) S) : Prop where
  theorem12_3_closed : ∀ {M N : Interpretation C S}, HomotopyEquivalent M N →
    ∀ φ, sem.Satisfies M φ ↔ sem.Satisfies N φ
end Helfer

/-- The matrix kernel as a subspace of Euclidean cochains. -/
def matrixHarmonicSubspace {N : Type} [Fintype N] (Δ : Matrix N N ℝ) :
    Submodule ℝ (EuclideanSpace ℝ N) :=
  LinearMap.ker ((Matrix.mulVecLin Δ).comp
    (WithLp.linearEquiv 2 ℝ (N → ℝ)).toLinearMap)
/-- Orthogonal projection of a cochain onto the selected matrix kernel. -/
def operativeHarmonicComponent {N : Type} [Fintype N]
    (Δ : Matrix N N ℝ) (b : EuclideanSpace ℝ N) : EuclideanSpace ℝ N :=
  (matrixHarmonicSubspace Δ).starProjection b

namespace HCPBridge
universe u₁ u₂ v₁ v₂ w uRep uAux
variable (C : Type u₂) [Category.{v₂} C] [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
  (S : Helfer.Signature.{u₁, v₁}) (sem : Helfer.ClosedSemantics (C := C) S)
  (Rep : Type uRep) (N : Type) [Fintype N] (P : Type)
/-- Semantic interpretations and operative Laplacians with a public classifier factoring through closed theory. -/
structure Realization where
  interpretation : Rep → Helfer.Interpretation C S
  laplacian : Rep → Matrix N N ℝ
  classifier : Rep → P
  publicProjection : Matrix N N ℝ → P
  classifyTheory : Set sem.ClosedFormula → P
  classifier_factors : ∀ r, classifier r = classifyTheory (Helfer.ClosedTheory sem (interpretation r))
  operator_classifier_factors : ∀ r, publicProjection (laplacian r) = classifier r
variable {C S sem Rep N P}
/-- Equivalent semantic cores with one input harmonic for the first operative operator and nonharmonic for the second. -/
structure KernelSeparationWitness (X : Realization C S sem Rep N P) where
  left : Rep
  right : Rep
  input : N → ℝ
  semanticEquivalence : Helfer.HomotopyEquivalent (X.interpretation left) (X.interpretation right)
  harmonic_left : MatrixIsHarmonic (X.laplacian left) input
  not_harmonic_right : ¬ MatrixIsHarmonic (X.laplacian right) input
/-- A public class value paired with the observed cochain. -/
abbrev Observation (P N : Type*) := P × (N → ℝ)
/-- A function from supplied auxiliary data and public observations to cochains. -/
abbrev Solver (Aux : Type uAux) (P N : Type) := Aux → Observation P N → (N → ℝ)
/-- Outputs lie in each admitted representative's operative kernel. -/
def SolverSoundOn (X : Realization C S sem Rep N P) {Aux : Type uAux}
    (solver : Solver Aux P N) (aux : Aux) : Prop :=
  ∀ r b, MatrixIsHarmonic (X.laplacian r) (solver aux (X.classifier r, b))
/-- Already-harmonic inputs are returned unchanged for every admitted representative. -/
def SolverExactOnHarmonic (X : Realization C S sem Rep N P) {Aux : Type uAux}
    (solver : Solver Aux P N) (aux : Aux) : Prop :=
  ∀ r b, MatrixIsHarmonic (X.laplacian r) b → solver aux (X.classifier r, b) = b
/-- Outputs equal the representative-selected orthogonal projection at every observed cochain. -/
def SolverExactOnOperativeTarget (X : Realization C S sem Rep N P) {Aux : Type uAux}
    (solver : Solver Aux P N) (aux : Aux) : Prop :=
  ∀ r b, solver aux (X.classifier r, b) =
    (operativeHarmonicComponent (X.laplacian r) (WithLp.toLp 2 b) : N → ℝ)


end HCPBridge

/-- Three actual module carriers and the two actual square-zero coboundaries. -/
structure ThreeTermData where
  C0 : ModuleCat.{0} ℝ
  C1 : ModuleCat.{0} ℝ
  C2 : ModuleCat.{0} ℝ
  d0 : C0 ⟶ C1
  d1 : C1 ⟶ C2
  squareZero : d0 ≫ d1 = 0
namespace ThreeTermData
/-- The supplied module carriers in degrees zero, one and two, and the zero object elsewhere. -/
def term (D : ThreeTermData) (i : ℤ) : ModuleCat ℝ :=
  if i = 0 then D.C0 else if i = 1 then D.C1 else if i = 2 then D.C2 else 0
/-- The two supplied arrows in degrees zero and one, extended by zero. -/
def differential (D : ThreeTermData) (i : ℤ) : D.term i ⟶ D.term (i + 1) := by
  by_cases h0 : i = 0
  · subst i; exact D.d0
  by_cases h1 : i = 1
  · subst i; exact D.d1
  exact 0

theorem differential_comp (D : ThreeTermData) (i : ℤ) :
    D.differential i ≫ D.differential (i + 1) = 0 := by
  by_cases h0 : i = 0
  · subst i; exact D.squareZero
  by_cases h1 : i = 1
  · subst i; change D.d1 ≫ (0 : D.C2 ⟶ D.term 3) = 0; simp only [comp_zero]
  simp [differential, h0, h1]
/-- The integer-indexed cochain complex retaining the two supplied differentials. -/
def complex (D : ThreeTermData) : CochainComplex (ModuleCat ℝ) ℤ :=
  CochainComplex.of D.term D.differential D.differential_comp
end ThreeTermData

namespace AxisFamily
open CellularSheaf
open scoped BigOperators RealInnerProductSpace

theorem boundarySqZero (_v _f : Unit) :
    (Finset.univ : Finset Unit).sum (fun _ => (0 : ℤ) * 1) = 0 := by simp only [zero_mul, Finset.sum_const_zero]
/-- One vertex, edge and face with incidence numbers zero and one. -/
def complex : OrientedTwoComplex Unit Unit Unit where
  incidence01 _ _ := 0
  incidence12 _ _ := 1
  boundarySqZero := boundarySqZero
/-- The selected coordinate functional from the edge stalk to the face stalk. -/
def restriction (axis : Fin 2) : Coord 2 →ₗ[ℝ] Coord 1 where
  toFun b := WithLp.toLp 2 fun _ => b axis
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- A cellular sheaf with stalk dimensions zero, two and one and the selected coordinate restriction. -/
abbrev sheaf (axis : Fin 2) : CellularSheaf complex where
  vertexDim _ := 0
  edgeDim _ := 2
  faceDim _ := 1
  restrict01 _ _ := 0
  restrict12 _ _ := restriction axis
  restrict02 _ _ := 0
  restrictionComp _ _ _ h := False.elim (h rfl)
/-- The flattened coordinate index of the single two-dimensional edge stalk. -/
abbrev Index := TotalCoord Unit (fun _ => 2)
/-- The common Euclidean degree-one cochain space of the two presentations. -/
abbrev C1 := EuclideanSpace ℝ Index
/-- The unit vector in the selected edge coordinate. -/
def unitCochain (axis : Fin 2) : C1 := EuclideanSpace.single ⟨(), axis⟩ 1
@[simp] theorem unitCochain_apply (axis j : Fin 2) :
    unitCochain axis ⟨(), j⟩ = if j = axis then 1 else 0 := by
  simp [unitCochain, PiLp.single_apply, eq_comm]
/-- The complementary coordinate index in Fin 2. -/
def other (axis : Fin 2) : Fin 2 :=
  ⟨1 - axis.val, (Nat.sub_le 1 axis.val).trans_lt (Nat.lt_succ_self 1)⟩
@[simp] theorem other_zero : other 0 = 1 := rfl
@[simp] theorem other_one : other 1 = 0 := rfl
@[simp] theorem other_ne (axis : Fin 2) : other axis ≠ axis := by
  fin_cases axis <;> decide
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
    complex, sheaf, restriction, component, OrientedTwoComplex.incidence12Real]
  rfl
theorem delta1_adjoint_eq (axis : Fin 2) (c : (sheaf axis).C2) :
    (sheaf axis).delta1.adjoint c = EuclideanSpace.single ⟨(), axis⟩ (c ⟨(), 0⟩) := by
  apply ext_inner_left ℝ
  intro b
  rw [LinearMap.adjoint_inner_right, EuclideanSpace.inner_single_right]
  simp [PiLp.inner_apply, Fintype.sum_sigma, delta1_apply]
@[simp] theorem degreeOneLaplacian_apply (axis : Fin 2) (b : C1) (j : Fin 2) :
    (sheaf axis).degreeOneLaplacian b ⟨(), j⟩ = if j = axis then b ⟨(), axis⟩ else 0 := by
  simp [CellularSheaf.degreeOneLaplacian, LinearMap.comp_apply,
    delta1_adjoint_eq, PiLp.single_apply, eq_comm]
theorem harmonic_iff (axis : Fin 2) (b : C1) :
    (sheaf axis).IsHarmonicOneCochain b ↔ b ⟨(), axis⟩ = 0 := by
  constructor
  · intro h
    have hc := congrArg (fun x : C1 => x ⟨(), axis⟩) h
    simpa [CellularSheaf.IsHarmonicOneCochain] using hc
  · intro h
    change (sheaf axis).degreeOneLaplacian b = 0
    apply PiLp.ext
    rintro ⟨⟨⟩, j⟩
    simp [h]
/-- The full-rank integer-coordinate lattice in a real stalk. -/
def standardStalkLattice (n : ℕ) : StalkLattice n where
  presentation := { basis := 1, basis_injective := fun x y h =>
    (Matrix.one_mulVec x).symm.trans (h.trans (Matrix.one_mulVec y)) }
theorem standardStalkLattice_contains_iff (n : ℕ) (x : Coord n) :
    (standardStalkLattice n).Contains x ↔ ∃ z : Fin n → ℤ, ∀ i, x i = (z i : ℝ) := by
  change (∃ z : Fin n → ℤ, CVP.latticeVector (standardStalkLattice n).presentation z = ⇑x) ↔ _
  simp only [CVP.latticeVector, standardStalkLattice, Matrix.one_mulVec]
  constructor
  · rintro ⟨z, hz⟩; exact ⟨z, fun i => (congrFun hz i).symm⟩
  · rintro ⟨z, hz⟩; exact ⟨z, funext fun i => (hz i).symm⟩
theorem restriction_preserves (axis : Fin 2) :
    (standardStalkLattice 2).Preserves (standardStalkLattice 1) (restriction axis) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz⟩ := (standardStalkLattice_contains_iff 2 x).mp hx
  apply (standardStalkLattice_contains_iff 1 (restriction axis x)).mpr
  exact ⟨fun _ => z axis, fun _ => hz axis⟩
/-- Standard integer stalk lattices preserved by the cellular restriction maps. -/
def integralStructure (axis : Fin 2) : IntegralStructure (sheaf axis) where
  vertexStalk _ := standardStalkLattice 0
  edgeStalk _ := standardStalkLattice 2
  faceStalk _ := standardStalkLattice 1
  restrict01_preserves _ _ := by
    rintro _ ⟨x, hx, rfl⟩; exact (standardStalkLattice 2).carrier.zero_mem
  restrict12_preserves _ _ := restriction_preserves axis
  restrict02_preserves _ _ := by
    rintro _ ⟨x, hx, rfl⟩; exact (standardStalkLattice 1).carrier.zero_mem
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
  simp only [unitCochain_apply, Ne.symm (other_ne axis), ite_false]
/-- The unit integral harmonic message on the complementary axis. -/
def message (axis : Fin 2) : (integralStructure axis).harmonicOneLattice :=
  ⟨unitCochain (other axis), unitCochain_integral axis _, other_unit_harmonic axis⟩
/-- Zero exact opening and unit coexact opening in the face stalk. -/
def opening (axis : Fin 2) : HodgeNoise (sheaf axis) :=
  ⟨0, EuclideanSpace.single ⟨(), 0⟩ 1⟩
/-- The unit harmonic message together with its exact and coexact noise openings. -/
def sample (axis : Fin 2) : HodgeEncryptedCochain (integralStructure axis) :=
  ⟨message axis, opening axis⟩
/-- The unweighted test cochain e₀ + e₁. -/
def observed : C1 := unitCochain 0 + unitCochain 1
/-- The true cellular degree-one Hodge operator in the fixed Euclidean coordinate basis. -/
def laplacianMatrix (axis : Fin 2) : Matrix Index Index ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun Index ℝ).toBasis
    (EuclideanSpace.basisFun Index ℝ).toBasis (sheaf axis).degreeOneLaplacian
/-- The cellular carriers and both actual coboundaries as square-zero three-term data. -/
def cochainData (axis : Fin 2) : ThreeTermData where
  C0 := ModuleCat.of ℝ (sheaf axis).C0
  C1 := ModuleCat.of ℝ (sheaf axis).C1
  C2 := ModuleCat.of ℝ (sheaf axis).C2
  d0 := ModuleCat.ofHom (sheaf axis).delta0
  d1 := ModuleCat.ofHom (sheaf axis).delta1
  squareZero := ModuleCat.hom_ext ((sheaf axis).delta1_comp_delta0)
/-- The degrees with nonzero cohomology in the actual integer-indexed cellular complex. -/
def theory (axis : Fin 2) : Set ℤ :=
  {i | ¬ CategoryTheory.Limits.IsZero ((cochainData axis).complex.homology i)}
theorem harmonicBasis_injective (axis : Fin 2) :
    Function.Injective (Matrix.mulVec
      (fun (p : Index) (_ : Fin 1) => if p.2 = other axis then (1 : ℝ) else 0)) := by
  intro a b h
  have hc := congrFun h ⟨(), other axis⟩
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, ite_true, one_mul] at hc
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  simpa only [hj] using hc
/-- The rank-one integer lattice generated by the complementary coordinate unit vector. -/
def harmonicLattice (axis : Fin 2) : CVP.ExplicitLattice Index (Fin 1) where
  basis p _ := if p.2 = other axis then 1 else 0
  basis_injective := harmonicBasis_injective axis
theorem harmonicLatticeVector_eq (axis : Fin 2) (z : Fin 1 → ℤ) :
    WithLp.toLp 2 (CVP.latticeVector (harmonicLattice axis) z) =
      (z 0 : ℝ) • unitCochain (other axis) := by
  apply PiLp.ext
  rintro ⟨⟨⟩, j⟩
  simp [CVP.latticeVector, harmonicLattice, Matrix.mulVec, dotProduct, unitCochain_apply]
/-- Fixed integer coefficients: two in the first presentation and one in the second. -/
def weightedCoefficients (axis : Fin 2) : Fin 1 → ℤ := fun _ => if axis = 0 then 2 else 1
/-- Zero exact opening with face-stalk coexact coefficients one and two. -/
def weightedOpening (axis : Fin 2) : HodgeNoise (sheaf axis) :=
  ⟨0, EuclideanSpace.single ⟨(), 0⟩ (if axis = 0 then 1 else 2)⟩
theorem latticeVector_mem (axis : Fin 2) (z : Fin 1 → ℤ) :
    WithLp.toLp 2 (CVP.latticeVector (harmonicLattice axis) z) ∈
      (integralStructure axis).harmonicOneLattice := by
  rw [harmonicLatticeVector_eq, Int.cast_smul_eq_zsmul]
  exact (integralStructure axis).harmonicOneLattice.zsmul_mem (message axis).2 (z 0)
/-- The fixed integer lattice encoding with its complementary coexact noise opening. -/
def weightedSample (axis : Fin 2) : HodgeEncryptedCochain (integralStructure axis) :=
  ⟨⟨WithLp.toLp 2 (CVP.latticeVector (harmonicLattice axis) (weightedCoefficients axis)),
    latticeVector_mem axis _⟩, weightedOpening axis⟩
/-- The weighted test cochain e₀ + 2e₁. -/
def weightedObserved : C1 := unitCochain 0 + (2 : ℝ) • unitCochain 1


end AxisFamily
end
end HomotopicalEncryption.Palomar.PaperOne

namespace HomotopicalEncryption.Palomar.PaperOne
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ZeroObject
open scoped CochainComplex.Plus.modelCategoryQuillen
noncomputable section
namespace HCPBridge
universe u₁ u₂ v₁ v₂ w uRep uAux
variable {C : Type u₂} [Category.{v₂} C] [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
  {S : Helfer.Signature.{u₁, v₁}} {sem : Helfer.ClosedSemantics (C := C) S}
  {Rep : Type uRep} {N : Type} [Fintype N] {P : Type}
namespace Implementation
def latticeOfOwner {m n : Type} [Fintype n] (L : _root_.CVP.ExplicitLattice m n) :
    CVP.ExplicitLattice m n := ⟨L.basis, L.basis_injective⟩
def oracleOfOwner (O : _root_.CVP.Oracle N N) : CVP.Oracle N N := fun L t => O L.toOwner t
def oracleToOwner (O : CVP.Oracle N N) : _root_.CVP.Oracle N N := fun L t => O (latticeOfOwner L) t
theorem oracleOfOwner_correct {O : _root_.CVP.Oracle N N} (hO : _root_.CVP.OracleCorrect O) :
    CVP.OracleCorrect (oracleOfOwner O) := by intro L t; exact hO L.toOwner t
theorem oracleToOwner_correct {O : CVP.Oracle N N} (hO : CVP.OracleCorrect O) :
    _root_.CVP.OracleCorrect (oracleToOwner O) := by intro L t; exact hO (latticeOfOwner L) t
def signatureToOwner (S : Helfer.Signature.{u₁, v₁}) : _root_.HomotopicalEncryption.Helfer.Signature.{u₁, v₁} :=
  ⟨S.Sorts, S.FunctionSymbol⟩
def interpretationToOwner (M : Helfer.Interpretation C S) :
    _root_.HomotopicalEncryption.Helfer.Interpretation C (signatureToOwner S) :=
  ⟨M.onSort, fun {Γ} {B} f => M.onFunction (Γ := Γ) (B := B) f⟩
def interpretationOfOwner (M : _root_.HomotopicalEncryption.Helfer.Interpretation C (signatureToOwner S)) :
    Helfer.Interpretation C S :=
  ⟨M.onSort, fun {Γ} {B} f => M.onFunction (Γ := Γ) (B := B) f⟩
theorem interpretationOfToOwner (M : Helfer.Interpretation C S) :
    interpretationOfOwner (interpretationToOwner M) = M := by
  cases M
  rfl
def equivalenceToOwner {M M' : Helfer.Interpretation C S} (e : Helfer.HomotopyEquivalence M M') :
    _root_.HomotopicalEncryption.Helfer.HomotopyEquivalence (interpretationToOwner M) (interpretationToOwner M') where
  component A := e.component A
  preservesFunction := fun {Γ} {B} f => e.preservesFunction (Γ := Γ) (B := B) f
  sourceFibrant := e.sourceFibrant
  targetFibrant := e.targetFibrant
  sourceCofibrant := e.sourceCofibrant
  targetCofibrant := e.targetCofibrant
  componentWeakEquivalence := e.componentWeakEquivalence
def equivalenceOfOwner {M M' : _root_.HomotopicalEncryption.Helfer.Interpretation C (signatureToOwner S)}
    (e : _root_.HomotopicalEncryption.Helfer.HomotopyEquivalence M M') :
    Helfer.HomotopyEquivalence (interpretationOfOwner M) (interpretationOfOwner M') where
  component A := e.component A
  preservesFunction := fun {Γ} {B} f => e.preservesFunction (Γ := Γ) (B := B) f
  sourceFibrant := e.sourceFibrant
  targetFibrant := e.targetFibrant
  sourceCofibrant := e.sourceCofibrant
  targetCofibrant := e.targetCofibrant
  componentWeakEquivalence := e.componentWeakEquivalence
def semanticsToOwner (sem : Helfer.ClosedSemantics (C := C) S) :
    _root_.HomotopicalEncryption.Helfer.ClosedSemantics (C := C) (signatureToOwner S) where
  ClosedFormula := sem.ClosedFormula
  Satisfies M φ := sem.Satisfies (interpretationOfOwner M) φ
theorem invarianceToOwner (hInv : Helfer.ClosedFormulaInvariance sem) :
    _root_.HomotopicalEncryption.Helfer.ClosedFormulaInvariance (semanticsToOwner sem) where
  theorem12_3_closed := by
    intro M M' h φ
    exact hInv.theorem12_3_closed ⟨equivalenceOfOwner h.some⟩ φ
def realizationToOwner (X : Realization C S sem Rep N P) :
    _root_.HomotopicalEncryption.HCPBridge.Realization C (signatureToOwner S) (semanticsToOwner sem) Rep N ℝ P where
  interpretation r := interpretationToOwner (X.interpretation r)
  laplacian := X.laplacian
  classifier := ⟨X.classifier⟩
  publicProjection := X.publicProjection
  classifyTheory := X.classifyTheory
  classifier_factors r := by
    change X.classifier r = X.classifyTheory
      {φ | sem.Satisfies (interpretationOfOwner (interpretationToOwner (X.interpretation r))) φ}
    rw [interpretationOfToOwner]
    exact X.classifier_factors r
  operator_classifier_factors := X.operator_classifier_factors
def witnessToOwner {X : Realization C S sem Rep N P} (w : KernelSeparationWitness X) :
    _root_.HomotopicalEncryption.HCPBridge.KernelSeparationWitness (realizationToOwner X) where
  left := w.left
  right := w.right
  input := w.input
  semanticEquivalence := ⟨equivalenceToOwner w.semanticEquivalence.some⟩
  harmonic_left := w.harmonic_left
  not_harmonic_right := w.not_harmonic_right
end Implementation
/-- Typed semantic invariance plus independent kernel separation gives incompatible targets. -/
theorem operativeTargets_ne_of_kernelSeparation (X : Realization C S sem Rep N P)
    (hInv : Helfer.ClosedFormulaInvariance sem) (witness : KernelSeparationWitness X) :
    ∃ (p : P) (b : N → ℝ) (r s : Rep), X.classifier r = p ∧ X.classifier s = p ∧
      operativeHarmonicComponent (X.laplacian r) (WithLp.toLp 2 b) ≠
        operativeHarmonicComponent (X.laplacian s) (WithLp.toLp 2 b) := by
  obtain ⟨obs, wl, wr, hne⟩ := _root_.HomotopicalEncryption.HCPBridge.operativeTargets_ne_of_kernelSeparation
    (Implementation.realizationToOwner X) (Implementation.invarianceToOwner hInv)
    (Implementation.witnessToOwner witness)
  refine ⟨obs.1, obs.2, wl.representative, wr.representative, wl.class_eq, wr.class_eq, ?_⟩
  intro heq
  exact hne (congrArg WithLp.ofLp heq)
/-- Exact CVP access does not satisfy the manuscript's public Hodge solver contract. -/
theorem cvpOracle_insufficient_of_kernelSeparation (X : Realization C S sem Rep N P)
    (hInv : Helfer.ClosedFormulaInvariance sem) (witness : KernelSeparationWitness X)
    (hOracle : ∃ O : CVP.Oracle N N, CVP.OracleCorrect O) :
    ¬ ∃ solver : Solver (CVP.Oracle N N) P N, ∀ O, CVP.OracleCorrect O →
      SolverSoundOn X solver O ∧ SolverExactOnHarmonic X solver O := by
  rintro ⟨solver, hsolver⟩
  apply _root_.HomotopicalEncryption.HCPBridge.cvpOracle_insufficient_of_kernelSeparation
    (Implementation.realizationToOwner X) (Implementation.invarianceToOwner hInv)
    (Implementation.witnessToOwner witness)
    (by obtain ⟨O, hO⟩ := hOracle
        exact ⟨Implementation.oracleToOwner O, Implementation.oracleToOwner_correct hO⟩)
  refine ⟨fun O obs => solver (Implementation.oracleOfOwner O) obs, ?_⟩
  intro O hO
  exact hsolver _ (Implementation.oracleOfOwner_correct hO)
/-- Direct recovery has the same explicit oracle-existence and uniformity quantifiers. -/
theorem cvpOracle_insufficient_for_operativeTarget (X : Realization C S sem Rep N P)
    (hInv : Helfer.ClosedFormulaInvariance sem) (witness : KernelSeparationWitness X)
    (hOracle : ∃ O : CVP.Oracle N N, CVP.OracleCorrect O) :
    ¬ ∃ solver : Solver (CVP.Oracle N N) P N, ∀ O, CVP.OracleCorrect O →
      SolverExactOnOperativeTarget X solver O := by
  rintro ⟨solver, hsolver⟩
  apply _root_.HomotopicalEncryption.HCPBridge.cvpOracle_insufficient_for_operativeTarget
    (Implementation.realizationToOwner X) (Implementation.invarianceToOwner hInv)
    (Implementation.witnessToOwner witness)
    (by obtain ⟨O, hO⟩ := hOracle
        exact ⟨Implementation.oracleToOwner O, Implementation.oracleToOwner_correct hO⟩)
  refine ⟨fun O obs => solver (Implementation.oracleOfOwner O) obs, ?_⟩
  intro O hO obs w
  rcases obs with ⟨p, b⟩
  change solver (Implementation.oracleOfOwner O) (p, b) =
    (operativeHarmonicComponent (X.laplacian w.representative) (WithLp.toLp 2 b) : N → ℝ)
  have hs := hsolver _ (Implementation.oracleOfOwner_correct hO) w.representative b
  have hc : X.classifier w.representative = p := w.class_eq
  rw [hc] at hs
  exact hs
end HCPBridge
namespace AxisFamily
open CellularSheaf
namespace Implementation
theorem theory_eq_owner (axis : Fin 2) : theory axis = _root_.HomotopicalEncryption.HCP.AxisFamily.theory axis := rfl
theorem laplacian_eq_owner (axis : Fin 2) :
    laplacianMatrix axis = _root_.HomotopicalEncryption.Sheaf.HCPAxisFamily.laplacianMatrix axis := rfl
theorem sample_observed_eq_owner (axis : Fin 2) :
    (sample axis).observed = (_root_.HomotopicalEncryption.Sheaf.HCPAxisFamily.sample axis).observed := rfl
theorem sample_message_eq_owner (axis : Fin 2) :
    (sample axis).message.1 = (_root_.HomotopicalEncryption.Sheaf.HCPAxisFamily.sample axis).message.1 := rfl
theorem weighted_observed_eq_owner (axis : Fin 2) :
    (weightedSample axis).observed = (_root_.HomotopicalEncryption.HCP.AxisFamily.weightedSample axis).observed := rfl
theorem weighted_message_eq_owner (axis : Fin 2) :
    (weightedSample axis).message.1 = (_root_.HomotopicalEncryption.HCP.AxisFamily.weightedSample axis).message.1 := rfl
end Implementation
/-- The actual cellular complexes are isomorphic before taking cohomology. -/
theorem cellular_complex_iso :
    Nonempty ((cochainData 0).complex ≅ (cochainData 1).complex) := by
  exact ⟨(_root_.HomotopicalEncryption.Helfer.CochainModel.strictIso_of_isometricCochainEquiv
    _root_.HomotopicalEncryption.Sheaf.HCPAxisFamily.axisSwap).complexIso⟩

/-- One actual cellular observation has two nonzero integral targets and private CVP answers. -/
theorem cellular_axis_ambiguity :
    theory 0 = theory 1 ∧
    (∀ axis : Fin 2, (sample axis).observed = observed ∧
      (sample axis).opening.exactComponent = 0 ∧ (sample axis).message.1 ≠ 0 ∧
      operativeHarmonicComponent (laplacianMatrix axis) observed = (sample axis).message.1 ∧
      (∀ v, CVP.Solution ⟨harmonicLattice axis, (sample axis).observed⟩ v ↔
        v = (sample axis).message.1) ∧
      (∃! v, CVP.Solution ⟨harmonicLattice axis, (sample axis).observed⟩ v)) ∧
    (sample 0).message.1 ≠ (sample 1).message.1 := by
  refine ⟨?_, ?_, _root_.HomotopicalEncryption.Sheaf.HCPAxisFamily.sample_messages_ne⟩
  · rw [Implementation.theory_eq_owner, Implementation.theory_eq_owner]
    exact _root_.HomotopicalEncryption.HCP.AxisFamily.theory_zero_eq_one
  · intro axis
    refine ⟨_root_.HomotopicalEncryption.Sheaf.HCPAxisFamily.sample_observed axis,
      _root_.HomotopicalEncryption.Sheaf.HCPAxisFamily.sample_exactComponent axis,
      _root_.HomotopicalEncryption.HCP.AxisFamily.message_ne_zero axis, ?_,
      _root_.HomotopicalEncryption.HCP.AxisFamily.cvp_solution_iff_message axis,
      _root_.HomotopicalEncryption.HCP.AxisFamily.cvp_existsUnique axis⟩
    exact (_root_.HomotopicalEncryption.HCP.AxisFamily.operativeHarmonicComponent_eq axis observed).trans
      (_root_.HomotopicalEncryption.Sheaf.HCPAxisFamily.sample_projection axis)
/-- The actual family also defeats uniform public target recovery with a correct CVP oracle. -/
theorem cvp_oracle_insufficient
    (hOracle : ∃ O : CVP.Oracle Index Index, CVP.OracleCorrect O) :
    ¬ ∃ solver : HCPBridge.Solver (CVP.Oracle Index Index) (Set ℤ) Index,
      ∀ O, CVP.OracleCorrect O → ∀ axis b,
        solver O (theory axis, b) =
          (operativeHarmonicComponent (laplacianMatrix axis) (WithLp.toLp 2 b) : Index → ℝ) := by
  rintro ⟨solver, hsolver⟩
  apply _root_.HomotopicalEncryption.HCP.AxisFamily.cvp_oracle_insufficient
    (by obtain ⟨O, hO⟩ := hOracle
        exact ⟨HCPBridge.Implementation.oracleToOwner O,
          HCPBridge.Implementation.oracleToOwner_correct hO⟩)
  refine ⟨fun O obs => solver (HCPBridge.Implementation.oracleOfOwner O) obs, ?_⟩
  intro O hO obs w
  rcases obs with ⟨p, b⟩
  change solver (HCPBridge.Implementation.oracleOfOwner O) (p, b) =
    (operativeHarmonicComponent (laplacianMatrix w.representative) (WithLp.toLp 2 b) : Index → ℝ)
  have hs := hsolver _ (HCPBridge.Implementation.oracleOfOwner_correct hO) w.representative b
  have hc : theory w.representative = p :=
    (Implementation.theory_eq_owner w.representative).trans w.class_eq
  rw [hc] at hs
  exact hs
/-- Fixed integer encodings 2 and 1 share b=(1,2), but each private lattice has its own unique answer. -/
theorem weighted_axis_recovery_obstruction :
    (theory 0, ((weightedSample 0).observed : Index → ℝ)) =
      (theory 1, ((weightedSample 1).observed : Index → ℝ)) ∧
    (weightedCoefficients 0 0 = 2 ∧ weightedCoefficients 1 0 = 1) ∧
    (¬ ∃ decoder : Set ℤ × (Index → ℝ) → ℤ, ∀ axis,
      decoder (theory axis, (weightedSample axis).observed) = weightedCoefficients axis 0) ∧
    (∀ axis : Fin 2, (weightedSample axis).observed = weightedObserved ∧
      (weightedSample axis).opening.exactComponent = 0 ∧
      (weightedSample axis).message.1 ≠ 0 ∧
      (∀ v, CVP.Solution ⟨harmonicLattice axis, (weightedSample axis).observed⟩ v ↔
        v = (operativeHarmonicComponent (laplacianMatrix axis) weightedObserved : Index → ℝ)) ∧
      (∃! v, CVP.Solution ⟨harmonicLattice axis, (weightedSample axis).observed⟩ v)) := by
  refine ⟨?_, _root_.HomotopicalEncryption.HCP.AxisFamily.weighted_coefficients_values, ?_, ?_⟩
  · have h := _root_.HomotopicalEncryption.HCP.AxisFamily.weighted_public_observations_eq
    change (_root_.HomotopicalEncryption.HCP.AxisFamily.theory 0,
        ((_root_.HomotopicalEncryption.HCP.AxisFamily.weightedSample 0).observed : Index → ℝ)) =
      (_root_.HomotopicalEncryption.HCP.AxisFamily.theory 1,
        ((_root_.HomotopicalEncryption.HCP.AxisFamily.weightedSample 1).observed : Index → ℝ)) at h
    rw [Implementation.theory_eq_owner 0, Implementation.theory_eq_owner 1,
      Implementation.weighted_observed_eq_owner 0, Implementation.weighted_observed_eq_owner 1]
    exact h
  · rintro ⟨decoder, hdecoder⟩
    apply _root_.HomotopicalEncryption.HCP.AxisFamily.no_exact_encoded_message_decoder
    refine ⟨decoder, ?_⟩
    intro axis
    have h := hdecoder axis
    rw [Implementation.theory_eq_owner axis, Implementation.weighted_observed_eq_owner axis] at h
    change decoder (_root_.HomotopicalEncryption.HCP.AxisFamily.theory axis,
        ((_root_.HomotopicalEncryption.HCP.AxisFamily.weightedSample axis).observed : Index → ℝ)) =
      _root_.HomotopicalEncryption.HCP.AxisFamily.weightedCoefficients axis 0
    exact h
  · intro axis
    refine ⟨_root_.HomotopicalEncryption.HCP.AxisFamily.weightedSample_observed axis,
      _root_.HomotopicalEncryption.HCP.AxisFamily.weightedSample_exactComponent axis,
      _root_.HomotopicalEncryption.HCP.AxisFamily.weightedSample_message_ne_zero axis, ?_,
      _root_.HomotopicalEncryption.HCP.AxisFamily.weighted_cvp_existsUnique axis⟩
    intro v
    exact (_root_.HomotopicalEncryption.HCP.AxisFamily.weighted_cvp_solution_iff_operativeTarget axis v).trans
      (by rfl)
end AxisFamily
end
end HomotopicalEncryption.Palomar.PaperOne
