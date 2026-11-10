module

public import Laplacian.Projection

@[expose] public section

/-
  Grassmannian Laplacian search space.

  Paper correspondence:
  - Paper 1 Section 2: HCP hidden-kernel search space.
  - Paper 1 Section 3: comparison with explicitly presented CVP instances.

  This file names the family Ω_k of Laplacians induced by k-dimensional
  harmonic subspaces and proves the basic shape facts needed downstream.
  It deliberately contains no adversary model and no proximity projection.
-/

set_option linter.mathlibStandardSet false
set_option linter.unusedSectionVars false

open scoped BigOperators Real Nat Classical Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Matrix Real InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
Projection-facing Grassmannian point for hcrypt.

This uses the subspace convention directly: a rank-`r` harmonic subspace of the
ambient cochain space. This is the object whose orthogonal complement defines
the projection-model Laplacian `Δ_W = I - P_W`.
-/
structure HarmonicSubspace (n : Type*) [Fintype n] [DecidableEq n] (r : ℕ) where
  carrier : Submodule ℝ (EuclideanSpace ℝ n)
  rank_eq : Module.finrank ℝ carrier = r

namespace HarmonicSubspace

variable {r : ℕ}

instance : CoeOut (HarmonicSubspace n r) (Submodule ℝ (EuclideanSpace ℝ n)) :=
  ⟨HarmonicSubspace.carrier⟩

/-- The rank carried by a projection-facing Grassmannian point. -/
theorem finrank_carrier (W : HarmonicSubspace n r) :
    Module.finrank ℝ W.carrier = r :=
  W.rank_eq

/-- The Laplacian induced by a ranked harmonic subspace. -/
def toLaplacian (W : HarmonicSubspace n r) :
    Matrix n n ℝ :=
  @laplacian n _ _ W.carrier inferInstance

end HarmonicSubspace

/-- The set of Laplacians for rank-`r` harmonic subspaces.
    This is the search space Ω_r ≅ Gr(r,n) in the subspace convention. -/
def Ω (r : ℕ) : Set (Matrix n n ℝ) :=
  { A | ∃ W : HarmonicSubspace n r,
        ∃ h : W.carrier.HasOrthogonalProjection,
          A = @laplacian n _ _ W.carrier h }

/-- The set of Laplacians for 1-dimensional subspaces (projective space). -/
def Ω_1 : Set (Matrix n n ℝ) := Ω 1

namespace HarmonicSubspace

variable {r : ℕ}

/-- A ranked harmonic subspace determines a point of the corresponding Laplacian search space. -/
theorem toLaplacian_mem_Ω (W : HarmonicSubspace n r) :
    W.toLaplacian ∈ Ω r := by
  refine' ⟨W, inferInstance, rfl⟩

end HarmonicSubspace

/-- Ω k is a subset of the set of all Laplacians. -/
theorem Ω_subset_LaplacianSpace (r : ℕ) :
  Ω r ⊆ { A | ∃ W : Submodule ℝ (EuclideanSpace ℝ n),
    ∃ h : W.HasOrthogonalProjection, A = @laplacian n _ _ W h } := by
    intro A hA;
    rcases hA with ⟨W, hW, hA⟩
    exact ⟨W.carrier, hW, hA⟩

/-- There exists a subspace of dimension k if k ≤ n. -/
lemma exists_subspace_dim_k (k : ℕ) (hk : k ≤ Fintype.card n) :
  ∃ W : Submodule ℝ (EuclideanSpace ℝ n), Module.finrank ℝ W = k := by
    obtain ⟨s, hs⟩ : ∃ s : Finset n, s.card = k := by
      have := Finset.exists_subset_card_eq hk; tauto;
    refine' ⟨ Submodule.span ℝ ( Set.range ( fun i : s => EuclideanSpace.single ( i : n ) ( 1 : ℝ ) ) ), _ ⟩;
    rw [ finrank_span_eq_card ] ; aesop;
    refine' Fintype.linearIndependent_iff.2 _;
    intro g hg i; replace hg := congrArg (fun b : EuclideanSpace ℝ n => b i) hg; simp_all +decide;
    rw [ Finset.sum_eq_single i ] at hg <;> aesop

/-- Ω k is nonempty if k ≤ n.
    Python: grassmannian_laplacians(d, k) always returns results when k ≤ d. -/
theorem Ω_k_nonempty (k : ℕ) (hk : k ≤ Fintype.card n) : (@Ω n _ _ k).Nonempty := by
  obtain ⟨ W, hW ⟩ := exists_subspace_dim_k k hk;
  refine' ⟨ _, ⟨W, hW⟩, inferInstance, rfl ⟩

end
