module

public import Sheaf.Hodge

@[expose] public section

/-!
# Isometric equivalences of finite cellular cochain complexes

A linear bijection alone does not transport the Hodge Laplacian: the isometry
hypotheses are what make the adjoints commute with transport.
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

/--
A degreewise isometric equivalence between the cochain complexes underlying two
cellular sheaves on the same oriented two-complex.
-/
structure IsometricCochainEquiv (F G : CellularSheaf X) where
  degreeZero : F.C0 ≃ₗᵢ[ℝ] G.C0
  degreeOne : F.C1 ≃ₗᵢ[ℝ] G.C1
  degreeTwo : F.C2 ≃ₗᵢ[ℝ] G.C2
  delta0_commutes :
    degreeOne.toLinearEquiv.toLinearMap.comp F.delta0 =
      G.delta0.comp degreeZero.toLinearEquiv.toLinearMap
  delta1_commutes :
    degreeTwo.toLinearEquiv.toLinearMap.comp F.delta1 =
      G.delta1.comp degreeOne.toLinearEquiv.toLinearMap

namespace IsometricCochainEquiv

variable {F G : CellularSheaf X}

/-- The degree-zero adjoint square commutes with isometric transport. -/
theorem delta0_adjoint_naturality
    (e : IsometricCochainEquiv F G) (b : F.C1) :
    G.delta0.adjoint (e.degreeOne b) =
      e.degreeZero (F.delta0.adjoint b) := by
  apply ext_inner_left ℝ
  intro a
  rw [LinearMap.adjoint_inner_right]
  rw [← e.degreeZero.apply_symm_apply a]
  rw [e.degreeZero.inner_map_map]
  rw [LinearMap.adjoint_inner_right]
  have h :
      e.degreeOne (F.delta0 (e.degreeZero.symm a)) = G.delta0 a := by
    simpa using
      LinearMap.congr_fun e.delta0_commutes (e.degreeZero.symm a)
  simp only [e.degreeZero.apply_symm_apply]
  rw [← h]
  exact e.degreeOne.inner_map_map _ _

/-- The degree-one adjoint square commutes with isometric transport. -/
theorem delta1_adjoint_naturality
    (e : IsometricCochainEquiv F G) (c : F.C2) :
    G.delta1.adjoint (e.degreeTwo c) =
      e.degreeOne (F.delta1.adjoint c) := by
  apply ext_inner_left ℝ
  intro b
  rw [LinearMap.adjoint_inner_right]
  rw [← e.degreeOne.apply_symm_apply b]
  rw [e.degreeOne.inner_map_map]
  rw [LinearMap.adjoint_inner_right]
  have h :
      e.degreeTwo (F.delta1 (e.degreeOne.symm b)) = G.delta1 b := by
    simpa using
      LinearMap.congr_fun e.delta1_commutes (e.degreeOne.symm b)
  simp only [e.degreeOne.apply_symm_apply]
  rw [← h]
  exact e.degreeTwo.inner_map_map _ _

/-- The true degree-one Hodge Laplacian commutes with chain transport. -/
theorem degreeOneLaplacian_naturality
    (e : IsometricCochainEquiv F G) (b : F.C1) :
    G.degreeOneLaplacian (e.degreeOne b) =
      e.degreeOne (F.degreeOneLaplacian b) := by
  simp only [degreeOneLaplacian, LinearMap.add_apply, LinearMap.comp_apply]
  rw [e.delta0_adjoint_naturality b]
  have h0 :
      e.degreeOne (F.delta0 (F.delta0.adjoint b)) =
        G.delta0 (e.degreeZero (F.delta0.adjoint b)) := by
    simpa using
      LinearMap.congr_fun e.delta0_commutes (F.delta0.adjoint b)
  have h1 :
      e.degreeTwo (F.delta1 b) = G.delta1 (e.degreeOne b) := by
    simpa using LinearMap.congr_fun e.delta1_commutes b
  rw [← h0, ← h1]
  rw [e.delta1_adjoint_naturality (F.delta1 b)]
  exact (e.degreeOne.map_add _ _).symm

/--
Harmonicity is preserved when the cochain is transported together with its
hidden presentation.
-/
theorem isHarmonicOneCochain_iff
    (e : IsometricCochainEquiv F G) (b : F.C1) :
    F.IsHarmonicOneCochain b ↔
      G.IsHarmonicOneCochain (e.degreeOne b) := by
  simp only [IsHarmonicOneCochain]
  rw [e.degreeOneLaplacian_naturality b]
  exact e.degreeOne.toLinearEquiv.map_eq_zero_iff.symm

/-- The degree-one isometry maps the harmonic subspace onto the target one. -/
theorem map_harmonicOneSubspace
    (e : IsometricCochainEquiv F G) :
    Submodule.map e.degreeOne.toLinearEquiv.toLinearMap
        F.harmonicOneSubspace =
      G.harmonicOneSubspace := by
  ext y
  rw [Submodule.mem_map_equiv F.harmonicOneSubspace]
  change
    F.IsHarmonicOneCochain (e.degreeOne.symm y) ↔
      G.IsHarmonicOneCochain y
  simpa using e.isHarmonicOneCochain_iff (e.degreeOne.symm y)

/-- Kernel-level form of `map_harmonicOneSubspace`. -/
theorem map_ker_degreeOneLaplacian
    (e : IsometricCochainEquiv F G) :
    Submodule.map e.degreeOne.toLinearEquiv.toLinearMap
        (LinearMap.ker F.degreeOneLaplacian) =
      LinearMap.ker G.degreeOneLaplacian := by
  simpa [harmonicOneSubspace] using e.map_harmonicOneSubspace

end IsometricCochainEquiv

end CellularSheaf
end Sheaf
end HomotopicalEncryption
