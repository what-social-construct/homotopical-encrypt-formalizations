module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Finite oriented cell complexes through degree two

This module contains only the combinatorial substrate needed by the Paper 1
cellular-sheaf construction.  A complex has finite vertex, edge, and face
carriers, integer incidence numbers, and the actual boundary-square equation.

The carrier types and their `Fintype` instances remain parameters.  This keeps
the resulting cochain coordinate types transparent to Lean and avoids hiding
finite-dimensional instances behind structure projections.
-/

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace HomotopicalEncryption
namespace Sheaf

/--
An oriented finite cell complex in degrees zero, one, and two.

`incidence01 v e` is the coefficient of `v` in the boundary of `e`, while
`incidence12 e f` is the coefficient of `e` in the boundary of `f`.
`boundarySqZero` is the coefficientwise statement `∂₁ ∘ ∂₂ = 0`.

For a simplicial or regular cellular complex the nonzero coefficients are
normally `±1`; allowing general integer incidence numbers also covers the
usual oriented cellular-chain presentation without adding an unnecessary
regularity assumption.
-/
structure OrientedTwoComplex
    (Vertex Edge Face : Type*)
    [Fintype Vertex] [Fintype Edge] [Fintype Face] where
  incidence01 : Vertex → Edge → ℤ
  incidence12 : Edge → Face → ℤ
  boundarySqZero :
    ∀ v f,
      (Finset.univ : Finset Edge).sum
        (fun e => incidence01 v e * incidence12 e f) = 0

namespace OrientedTwoComplex

variable
  {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  (X : OrientedTwoComplex Vertex Edge Face)

/-- A vertex is incident to an edge exactly when its incidence is nonzero. -/
def VertexEdgeIncident (v : Vertex) (e : Edge) : Prop :=
  X.incidence01 v e ≠ 0

/-- An edge is incident to a face exactly when its incidence is nonzero. -/
def EdgeFaceIncident (e : Edge) (f : Face) : Prop :=
  X.incidence12 e f ≠ 0

/-- Vertex-to-edge incidences as real coefficients for Euclidean cochains. -/
def incidence01Real (v : Vertex) (e : Edge) : ℝ :=
  X.incidence01 v e

/-- Edge-to-face incidences as real coefficients for Euclidean cochains. -/
def incidence12Real (e : Edge) (f : Face) : ℝ :=
  X.incidence12 e f

@[simp]
theorem incidence01Real_ne_zero_iff (v : Vertex) (e : Edge) :
    X.incidence01Real v e ≠ 0 ↔ X.VertexEdgeIncident v e := by
  simp [incidence01Real, VertexEdgeIncident]

@[simp]
theorem incidence12Real_ne_zero_iff (e : Edge) (f : Face) :
    X.incidence12Real e f ≠ 0 ↔ X.EdgeFaceIncident e f := by
  simp [incidence12Real, EdgeFaceIncident]

/-- The boundary-square equation after the canonical scalar extension to `ℝ`. -/
theorem boundarySqZero_real (v : Vertex) (f : Face) :
    (Finset.univ : Finset Edge).sum
      (fun e => X.incidence01Real v e * X.incidence12Real e f) = 0 := by
  simp only [incidence01Real, incidence12Real]
  have h := congrArg (fun z : ℤ => (z : ℝ)) (X.boundarySqZero v f)
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_zero] using h

end OrientedTwoComplex

end Sheaf
end HomotopicalEncryption
