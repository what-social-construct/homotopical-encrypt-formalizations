module

public import Sheaf.HarmonicLattice

@[expose] public section

/-!
# What the exact-component view forgets about a full Hodge observation

The source score here is the existing kernel-normalized Hodge residual
`‖F.kernelNormalizedDegreeOneLaplacian E.observed‖`; it is not replaced by
a pullback score. A nonzero coexact direction gives an unbounded family of
existing Hodge samples whose exact components are all zero.

Consequently, an extraction depending only on that exact component cannot
preserve a positive far region on the unrestricted Hodge-noise carrier when
its zero image has target distance zero. This does not disprove a theorem
on a restricted, authenticated or noise-bounded application profile.
-/

set_option autoImplicit false

noncomputable section

namespace Hcrypt
namespace Sheaf
namespace CellularSheaf

variable
  {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : OrientedTwoComplex Vertex Edge Face}
  {F : CellularSheaf X}

namespace HodgeEncryptedCochain

variable {I : IntegralStructure F}

/-- The full-observation residual retains all exact and coexact noise. -/
theorem kernelNormalizedDegreeOneLaplacian_observed
    (E : HodgeEncryptedCochain I) :
    F.kernelNormalizedDegreeOneLaplacian E.observed = E.opening.value := by
  rw [F.kernelNormalizedDegreeOneLaplacian_apply,
    E.harmonicOneProjection_observed, observed]
  abel

/-- Zero message and exact opening, with a scaled coexact opening. This is
an element of the existing unrestricted Hodge sample carrier. -/
def coexactRay (I : IntegralStructure F) (v : F.C2) (t : ℝ) :
    HodgeEncryptedCochain I where
  message := 0
  opening := ⟨0, t • v⟩

@[simp]
theorem coexactRay_exactComponent
    (I : IntegralStructure F) (v : F.C2) (t : ℝ) :
    (coexactRay I v t).opening.exactComponent = 0 := by
  simp [coexactRay, HodgeNoise.exactComponent]

@[simp]
theorem coexactRay_observed
    (I : IntegralStructure F) (v : F.C2) (t : ℝ) :
    (coexactRay I v t).observed = t • F.delta1.adjoint v := by
  simp [coexactRay, observed, HodgeNoise.value]

/-- Every point on the ray has the same exact-component view. -/
theorem coexactRay_same_exactComponent
    (I : IntegralStructure F) (v : F.C2) (s t : ℝ) :
    (coexactRay I v s).opening.exactComponent =
      (coexactRay I v t).opening.exactComponent := by
  simp

/-- The actual kernel-normalized residual grows linearly along the forgotten
coexact direction. -/
theorem coexactRay_residual_norm
    (I : IntegralStructure F) (v : F.C2) (t : ℝ) :
    ‖F.kernelNormalizedDegreeOneLaplacian (coexactRay I v t).observed‖ =
      |t| * ‖F.delta1.adjoint v‖ := by
  rw [kernelNormalizedDegreeOneLaplacian_observed]
  simp [coexactRay, HodgeNoise.value, norm_smul, Real.norm_eq_abs]

/-- A nonzero coexact direction yields arbitrarily large original residuals
while its exact-component view remains zero. -/
theorem exists_coexactRay_residual_gt
    (I : IntegralStructure F) (v : F.C2)
    (hv : F.delta1.adjoint v ≠ 0) (bound : ℝ) :
    ∃ t : ℝ, 0 < t ∧
      (coexactRay I v t).opening.exactComponent = 0 ∧
      bound < ‖F.kernelNormalizedDegreeOneLaplacian
        (coexactRay I v t).observed‖ := by
  obtain ⟨t, ht, hbound⟩ := exists_pos_lt_mul (norm_pos_iff.mpr hv) bound
  refine ⟨t, ht, coexactRay_exactComponent I v t, ?_⟩
  rw [coexactRay_residual_norm, abs_of_pos ht]
  exact hbound

/-- The original residual norm does not descend to the exact-component view
on the unrestricted carrier when a nonzero coexact direction is present. -/
theorem not_residual_norm_factors_exactComponent
    (I : IntegralStructure F) (v : F.C2)
    (hv : F.delta1.adjoint v ≠ 0) :
    ¬ ∃ score : F.C1 → ℝ, ∀ E : HodgeEncryptedCochain I,
      score E.opening.exactComponent =
        ‖F.kernelNormalizedDegreeOneLaplacian E.observed‖ := by
  rintro ⟨score, hscore⟩
  have hzero := hscore (coexactRay I v 0)
  have hone := hscore (coexactRay I v 1)
  simp only [coexactRay_exactComponent, coexactRay_residual_norm,
    abs_zero, zero_mul] at hzero
  simp only [coexactRay_exactComponent, coexactRay_residual_norm,
    abs_one, one_mul] at hone
  have hnorm : ‖F.delta1.adjoint v‖ = 0 := hone.symm.trans hzero
  exact hv (norm_eq_zero.mp hnorm)

/-- No exact-component extraction whose zero image has target distance zero
can preserve a positive far region for all unrestricted Hodge samples.
The source radius is arbitrary; the counterexample has an even larger
actual residual and a zero-distance extracted value. -/
theorem not_far_preserving_exactComponent
    (I : IntegralStructure F) (v : F.C2)
    (hv : F.delta1.adjoint v ≠ 0)
    {Target : Type*} (extract : F.C1 → Target)
    (targetDistance : Target → ℝ)
    (hzero : targetDistance (extract 0) = 0)
    (sourceRadius targetRadius : ℝ) (hTarget : 0 < targetRadius) :
    ¬ (∀ E : HodgeEncryptedCochain I,
      sourceRadius ≤ ‖F.kernelNormalizedDegreeOneLaplacian E.observed‖ →
      targetRadius ≤ targetDistance (extract E.opening.exactComponent)) := by
  intro hfar
  obtain ⟨t, _ht, hexact, hlarge⟩ :=
    exists_coexactRay_residual_gt I v hv sourceRadius
  have htarget := hfar (coexactRay I v t) hlarge.le
  rw [hexact, hzero] at htarget
  exact (not_le_of_gt hTarget) htarget

/-- Zero-preserving extractions into a pointed target give the same
obstruction when the target's distance at zero vanishes. -/
theorem not_far_preserving_exactComponent_of_map_zero
    (I : IntegralStructure F) (v : F.C2)
    (hv : F.delta1.adjoint v ≠ 0)
    {Target : Type*} [Zero Target]
    (extract : F.C1 → Target) (hExtract : extract 0 = 0)
    (targetDistance : Target → ℝ) (hzero : targetDistance 0 = 0)
    (sourceRadius targetRadius : ℝ) (hTarget : 0 < targetRadius) :
    ¬ (∀ E : HodgeEncryptedCochain I,
      sourceRadius ≤ ‖F.kernelNormalizedDegreeOneLaplacian E.observed‖ →
      targetRadius ≤ targetDistance (extract E.opening.exactComponent)) := by
  apply not_far_preserving_exactComponent I v hv extract targetDistance
    (sourceRadius := sourceRadius) (targetRadius := targetRadius)
  · rw [hExtract, hzero]
  · exact hTarget

end HodgeEncryptedCochain
end CellularSheaf
end Sheaf
end Hcrypt

end
