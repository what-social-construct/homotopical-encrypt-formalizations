module

public import Sheaf.CellComplex
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

/-!
# Finite coordinate cellular sheaves

This module gives the concrete Paper 1 sheaf/cochain core.  Following the
face-to-coface convention used for cellular sheaves, the structure maps are
covariant along incidences:

`vertex stalk → edge stalk → face stalk`.

The cochain carriers are finite Euclidean direct sums.  Their coboundaries are
assembled from signed incidence coefficients and the actual stalk maps.  The
theorem `delta1_comp_delta0` derives `δ₁ ∘ δ₀ = 0` from the cell-complex
boundary equation and functorial composition of restriction maps; square-zero
is not an independent sheaf axiom here.
-/

set_option autoImplicit false

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace HomotopicalEncryption
namespace Sheaf

/-- Concrete coordinate model for a finite-dimensional real stalk. -/
abbrev Coord (n : ℕ) := EuclideanSpace ℝ (Fin n)

/--
A finite coordinate cellular sheaf on an oriented two-complex.

Only maps on nonzero incidences contribute to a coboundary.  `restrict02`
records the direct vertex-to-face map, and `restrictionComp` is the truncated
functor-composition law on every incident flag `v < e < f`.
-/
structure CellularSheaf
    {Vertex Edge Face : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face]
    (X : OrientedTwoComplex Vertex Edge Face) where
  vertexDim : Vertex → ℕ
  edgeDim : Edge → ℕ
  faceDim : Face → ℕ
  restrict01 :
    ∀ v e, Coord (vertexDim v) →ₗ[ℝ] Coord (edgeDim e)
  restrict12 :
    ∀ e f, Coord (edgeDim e) →ₗ[ℝ] Coord (faceDim f)
  restrict02 :
    ∀ v f, Coord (vertexDim v) →ₗ[ℝ] Coord (faceDim f)
  restrictionComp :
    ∀ v e f,
      X.VertexEdgeIncident v e →
      X.EdgeFaceIncident e f →
      (restrict12 e f).comp (restrict01 v e) = restrict02 v f

namespace CellularSheaf

variable
  {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : OrientedTwoComplex Vertex Edge Face}

/-- The flattened coordinate index of a finite family of stalks. -/
abbrev TotalCoord (Cell : Type*) (dim : Cell → ℕ) :=
  Σ c : Cell, Fin (dim c)

/-- A finite stalkwise direct product, represented as one Euclidean space. -/
abbrev Cochain (Cell : Type*) [Fintype Cell] (dim : Cell → ℕ) :=
  EuclideanSpace ℝ (TotalCoord Cell dim)

/-- Degree-zero cellular cochains. -/
abbrev C0 (F : CellularSheaf X) := Cochain Vertex F.vertexDim

/-- Degree-one cellular cochains. -/
abbrev C1 (F : CellularSheaf X) := Cochain Edge F.edgeDim

/-- Degree-two cellular cochains. -/
abbrev C2 (F : CellularSheaf X) := Cochain Face F.faceDim

/-- Project a flattened cochain onto one cell stalk. -/
def component
    {Cell : Type*} [Fintype Cell]
    (dim : Cell → ℕ) (c : Cell) :
    Cochain Cell dim →ₗ[ℝ] Coord (dim c) where
  toFun x := WithLp.toLp 2 (fun i => x ⟨c, i⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Assemble one stalk-valued block row per cell into a cochain map. -/
def assemble
    {Cell A : Type*} [Fintype Cell]
    [AddCommMonoid A] [Module ℝ A]
    (dim : Cell → ℕ)
    (L : ∀ c, A →ₗ[ℝ] Coord (dim c)) :
    A →ₗ[ℝ] Cochain Cell dim where
  toFun x := WithLp.toLp 2 (fun p : TotalCoord Cell dim => L p.1 x p.2)
  map_add' x y := by
    apply PiLp.ext
    intro p
    simp
  map_smul' a x := by
    apply PiLp.ext
    intro p
    simp

/-- One target-edge block row of the degree-zero coboundary. -/
def delta0At (F : CellularSheaf X) (e : Edge) :
    F.C0 →ₗ[ℝ] Coord (F.edgeDim e) :=
  (Finset.univ : Finset Vertex).sum fun v =>
    X.incidence01Real v e •
      (F.restrict01 v e).comp (component F.vertexDim v)

/-- One target-face block row of the degree-one coboundary. -/
def delta1At (F : CellularSheaf X) (f : Face) :
    F.C1 →ₗ[ℝ] Coord (F.faceDim f) :=
  (Finset.univ : Finset Edge).sum fun e =>
    X.incidence12Real e f •
      (F.restrict12 e f).comp (component F.edgeDim e)

/-- The cellular coboundary `δ₀ : C⁰ → C¹`. -/
def delta0 (F : CellularSheaf X) : F.C0 →ₗ[ℝ] F.C1 :=
  assemble F.edgeDim (delta0At F)

/-- The cellular coboundary `δ₁ : C¹ → C²`. -/
def delta1 (F : CellularSheaf X) : F.C1 →ₗ[ℝ] F.C2 :=
  assemble F.faceDim (delta1At F)

/--
Incidence-weighted restriction composition, including both zero-incidence
cases.  This is the local calculation used in the square-zero proof.
-/
lemma weightedRestrictionComp
    (F : CellularSheaf X)
    (v : Vertex) (e : Edge) (f : Face)
    (x : Coord (F.vertexDim v)) :
    X.incidence12Real e f •
        F.restrict12 e f
          (X.incidence01Real v e • F.restrict01 v e x) =
      (X.incidence01Real v e * X.incidence12Real e f) •
        F.restrict02 v f x := by
  by_cases h01 : X.incidence01Real v e = 0
  · simp [h01]
  by_cases h12 : X.incidence12Real e f = 0
  · simp [h12]
  rw [map_smul, smul_smul, mul_comm, ← LinearMap.comp_apply]
  rw [F.restrictionComp v e f
    ((X.incidence01Real_ne_zero_iff v e).mp h01)
    ((X.incidence12Real_ne_zero_iff e f).mp h12)]

/-- The face component of `δ₁(δ₀ x)` vanishes. -/
lemma delta1_delta0_at
    (F : CellularSheaf X) (x : F.C0) (f : Face) :
    F.delta1At f (F.delta0 x) = 0 := by
  simp only [delta0, assemble, delta0At, delta1At, component,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  change
    (Finset.univ : Finset Edge).sum (fun e =>
      X.incidence12Real e f • F.restrict12 e f
        ((Finset.univ : Finset Vertex).sum fun v =>
          X.incidence01Real v e •
            F.restrict01 v e ((component F.vertexDim v) x))) = 0
  simp_rw [map_sum, Finset.smul_sum]
  simp_rw [weightedRestrictionComp]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro v _
  rw [← Finset.sum_smul, X.boundarySqZero_real v f]
  simp

/-- The concrete cellular coboundaries satisfy `δ₁ ∘ δ₀ = 0`. -/
theorem delta1_comp_delta0 (F : CellularSheaf X) :
    F.delta1.comp F.delta0 = 0 := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro p
  rcases p with ⟨f, i⟩
  exact congrArg (fun y : Coord (F.faceDim f) => y i) (F.delta1_delta0_at x f)

/-- A degree-zero global section is a compatible vertex assignment. -/
def IsGlobalSection (F : CellularSheaf X) (x : F.C0) : Prop :=
  F.delta0 x = 0

/-- A closed degree-one cochain. -/
def IsOneCocycle (F : CellularSheaf X) (b : F.C1) : Prop :=
  F.delta1 b = 0

/-- An exact degree-one cochain. -/
def IsExactOneCochain (F : CellularSheaf X) (b : F.C1) : Prop :=
  ∃ a : F.C0, F.delta0 a = b

/-- Every exact degree-one cochain is a cocycle. -/
theorem isOneCocycle_of_isExactOneCochain
    (F : CellularSheaf X) {b : F.C1}
    (hb : F.IsExactOneCochain b) :
    F.IsOneCocycle b := by
  obtain ⟨a, rfl⟩ := hb
  change F.delta1 (F.delta0 a) = 0
  have h := LinearMap.congr_fun F.delta1_comp_delta0 a
  simpa using h

end CellularSheaf

end Sheaf
end HomotopicalEncryption
