module

public import Sheaf.Cellular
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

/-!
# Degree-one Hodge operators for the finite cellular-sheaf core

This file constructs the true degree-one Hodge--Laplacian from the concrete
cellular coboundaries.  The kernel-normalized operator is defined separately:
it has the same kernel, but is not identified with the Hodge operator or its
positive spectrum.
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

/-- The true degree-one Hodge operator `δ₀δ₀* + δ₁*δ₁`. -/
def degreeOneLaplacian (F : CellularSheaf X) : F.C1 →ₗ[ℝ] F.C1 :=
  F.delta0.comp F.delta0.adjoint + F.delta1.adjoint.comp F.delta1

/-- Harmonicity for degree-one cochains. -/
def IsHarmonicOneCochain (F : CellularSheaf X) (b : F.C1) : Prop :=
  F.degreeOneLaplacian b = 0

/-- A degree-one cochain is coclosed when it lies in `ker δ₀*`. -/
def IsCoclosedOneCochain (F : CellularSheaf X) (b : F.C1) : Prop :=
  F.delta0.adjoint b = 0

/-- A degree-one cochain is coexact when it lies in `im δ₁*`. -/
def IsCoexactOneCochain (F : CellularSheaf X) (b : F.C1) : Prop :=
  ∃ c : F.C2, F.delta1.adjoint c = b

/-- The degree-one Hodge operator is positive. -/
theorem degreeOneLaplacian_isPositive (F : CellularSheaf X) :
    F.degreeOneLaplacian.IsPositive := by
  exact (LinearMap.isPositive_self_comp_adjoint F.delta0).add
    (LinearMap.isPositive_adjoint_comp_self F.delta1)

/-- The degree-one Hodge operator is symmetric. -/
theorem degreeOneLaplacian_isSymmetric (F : CellularSheaf X) :
    F.degreeOneLaplacian.IsSymmetric :=
  F.degreeOneLaplacian_isPositive.isSymmetric

/-- The Hodge quadratic form is the sum of coclosed and cocycle energies. -/
theorem degreeOneLaplacian_energy
    (F : CellularSheaf X) (b : F.C1) :
    inner ℝ (F.degreeOneLaplacian b) b =
      ‖F.delta0.adjoint b‖ ^ 2 + ‖F.delta1 b‖ ^ 2 := by
  simp only [degreeOneLaplacian, LinearMap.add_apply, inner_add_left,
    LinearMap.comp_apply]
  rw [← LinearMap.adjoint_inner_right F.delta0 (F.delta0.adjoint b) b]
  rw [LinearMap.adjoint_inner_left F.delta1 b (F.delta1 b)]
  simp only [real_inner_self_eq_norm_sq]

/-- Harmonicity is exactly simultaneous coclosedness and closedness. -/
theorem degreeOneLaplacian_apply_eq_zero_iff
    (F : CellularSheaf X) (b : F.C1) :
    F.degreeOneLaplacian b = 0 ↔
      F.delta0.adjoint b = 0 ∧ F.delta1 b = 0 := by
  constructor
  · intro hb
    have henergy :
        ‖F.delta0.adjoint b‖ ^ 2 + ‖F.delta1 b‖ ^ 2 = 0 := by
      rw [← F.degreeOneLaplacian_energy b, hb]
      simp
    have hparts :=
      (add_eq_zero_iff_of_nonneg
        (sq_nonneg ‖F.delta0.adjoint b‖)
        (sq_nonneg ‖F.delta1 b‖)).mp henergy
    exact
      ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp hparts.1),
       norm_eq_zero.mp (sq_eq_zero_iff.mp hparts.2)⟩
  · rintro ⟨h0, h1⟩
    simp [degreeOneLaplacian, h0, h1]

theorem isHarmonicOneCochain_iff_coclosed_and_cocycle
    (F : CellularSheaf X) (b : F.C1) :
    F.IsHarmonicOneCochain b ↔
      F.IsCoclosedOneCochain b ∧ F.IsOneCocycle b := by
  simpa [IsHarmonicOneCochain, IsCoclosedOneCochain, IsOneCocycle]
    using F.degreeOneLaplacian_apply_eq_zero_iff b

/-- The exact degree-one subspace `im δ₀`. -/
def exactOneSubspace (F : CellularSheaf X) : Submodule ℝ F.C1 :=
  LinearMap.range F.delta0

/-- The harmonic degree-one subspace `ker Δ₁`. -/
def harmonicOneSubspace (F : CellularSheaf X) : Submodule ℝ F.C1 :=
  LinearMap.ker F.degreeOneLaplacian

/-- The coexact degree-one subspace `im δ₁*`. -/
def coexactOneSubspace (F : CellularSheaf X) : Submodule ℝ F.C1 :=
  LinearMap.range F.delta1.adjoint

theorem ker_degreeOneLaplacian (F : CellularSheaf X) :
    LinearMap.ker F.degreeOneLaplacian =
      LinearMap.ker F.delta0.adjoint ⊓ LinearMap.ker F.delta1 := by
  ext b
  simp only [LinearMap.mem_ker, Submodule.mem_inf]
  exact F.degreeOneLaplacian_apply_eq_zero_iff b

theorem inner_delta0_harmonic_eq_zero
    (F : CellularSheaf X) (a : F.C0) {h : F.C1}
    (hh : F.IsHarmonicOneCochain h) :
    inner ℝ (F.delta0 a) h = 0 := by
  have hc :=
    (F.isHarmonicOneCochain_iff_coclosed_and_cocycle h).mp hh
  rw [← LinearMap.adjoint_inner_right F.delta0 a h, hc.1]
  simp

theorem inner_harmonic_delta1Adjoint_eq_zero
    (F : CellularSheaf X) {h : F.C1} (c : F.C2)
    (hh : F.IsHarmonicOneCochain h) :
    inner ℝ h (F.delta1.adjoint c) = 0 := by
  have hc :=
    (F.isHarmonicOneCochain_iff_coclosed_and_cocycle h).mp hh
  rw [LinearMap.adjoint_inner_right F.delta1 h c, hc.2]
  simp

theorem inner_delta0_delta1Adjoint_eq_zero
    (F : CellularSheaf X) (a : F.C0) (c : F.C2) :
    inner ℝ (F.delta0 a) (F.delta1.adjoint c) = 0 := by
  rw [LinearMap.adjoint_inner_right F.delta1 (F.delta0 a) c]
  have hsquare := LinearMap.congr_fun F.delta1_comp_delta0 a
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hsquare
  rw [hsquare]
  simp

theorem exactOneSubspace_isOrtho_harmonicOneSubspace
    (F : CellularSheaf X) :
    F.exactOneSubspace ⟂ F.harmonicOneSubspace := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro x hx h hh
  rcases hx with ⟨a, rfl⟩
  apply F.inner_delta0_harmonic_eq_zero a
  exact LinearMap.mem_ker.mp hh

theorem harmonicOneSubspace_isOrtho_coexactOneSubspace
    (F : CellularSheaf X) :
    F.harmonicOneSubspace ⟂ F.coexactOneSubspace := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro h hh x hx
  rcases hx with ⟨c, rfl⟩
  apply F.inner_harmonic_delta1Adjoint_eq_zero c
  exact LinearMap.mem_ker.mp hh

theorem exactOneSubspace_isOrtho_coexactOneSubspace
    (F : CellularSheaf X) :
    F.exactOneSubspace ⟂ F.coexactOneSubspace := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro x hx y hy
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨c, rfl⟩
  exact F.inner_delta0_delta1Adjoint_eq_zero a c

/-- Orthogonal projection onto the harmonic degree-one subspace. -/
def harmonicOneProjection (F : CellularSheaf X) : F.C1 →ₗ[ℝ] F.C1 :=
  F.harmonicOneSubspace.starProjection.toLinearMap

/--
The kernel-normalized degree-one operator `I - P_(ker Δ₁)`. It shares the
Hodge kernel, but equality with `degreeOneLaplacian` is not claimed.
-/
def kernelNormalizedDegreeOneLaplacian
    (F : CellularSheaf X) : F.C1 →ₗ[ℝ] F.C1 :=
  F.harmonicOneSubspace.orthogonal.starProjection.toLinearMap

theorem kernelNormalizedDegreeOneLaplacian_apply
    (F : CellularSheaf X) (b : F.C1) :
    F.kernelNormalizedDegreeOneLaplacian b =
      b - F.harmonicOneProjection b := by
  unfold kernelNormalizedDegreeOneLaplacian harmonicOneProjection
  rw [eq_sub_iff_add_eq]
  rw [add_comm]
  exact F.harmonicOneSubspace.starProjection_add_starProjection_orthogonal b

theorem kernelNormalizedDegreeOneLaplacian_apply_eq_zero_iff
    (F : CellularSheaf X) (b : F.C1) :
  F.kernelNormalizedDegreeOneLaplacian b = 0 ↔
      b ∈ F.harmonicOneSubspace := by
  unfold kernelNormalizedDegreeOneLaplacian
  change F.harmonicOneSubspace.orthogonal.starProjection b = 0 ↔
    b ∈ F.harmonicOneSubspace
  rw [Submodule.starProjection_apply_eq_zero_iff]
  simp only [Submodule.orthogonal_orthogonal]

theorem ker_kernelNormalizedDegreeOneLaplacian
    (F : CellularSheaf X) :
    LinearMap.ker F.kernelNormalizedDegreeOneLaplacian =
      LinearMap.ker F.degreeOneLaplacian := by
  ext b
  simpa [harmonicOneSubspace, LinearMap.mem_ker] using
    F.kernelNormalizedDegreeOneLaplacian_apply_eq_zero_iff b

end CellularSheaf
end Sheaf
end HomotopicalEncryption
