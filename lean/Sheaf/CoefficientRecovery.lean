module

public import Sheaf.HarmonicLattice

@[expose] public section

/-!
# Exact recovery of presented harmonic-lattice coefficients

The recipient projects the actual observed cochain using the selected private
Hodge presentation, then inverts its explicit integer lattice encoding. This
partial decoder reads the observed cochain, not the message field of a sample.

Only the chosen presented harmonic sublattice is decoded. Full real span does
not assert that every intrinsic integral harmonic cochain lies in that lattice.
The decoder is classical and noncomputable; no efficient algorithm, finite
wire encoding, key delivery or cryptographic secrecy is supplied here.
-/

set_option autoImplicit false

noncomputable section

namespace HomotopicalEncryption.Sheaf.CellularSheaf

variable
  {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : OrientedTwoComplex Vertex Edge Face}
  {F : CellularSheaf X} {I : IntegralStructure F}
  {Rank : Type*} [Fintype Rank]

namespace HarmonicLatticePresentation

/-- Integer coefficients are unique in the selected full-column-rank presentation. -/
theorem point_injective (H : HarmonicLatticePresentation I Rank) :
    Function.Injective H.point := by
  intro z w h
  have hpoint := congrArg Subtype.val h
  change WithLp.toLp 2 (CVP.latticeVector H.lattice z) =
    WithLp.toLp 2 (CVP.latticeVector H.lattice w) at hpoint
  have hvectors := congrArg WithLp.ofLp hpoint
  change CVP.latticeVector H.lattice z = CVP.latticeVector H.lattice w at hvectors
  have hcasts := H.lattice.basis_injective hvectors
  funext j
  exact_mod_cast congrFun hcasts j

/-- Project the observed cochain and decode it only when the resulting point
belongs to the chosen presented integer lattice. -/
def decodeCoefficients (H : HarmonicLatticePresentation I Rank) (b : F.C1) :
    Option (Rank → ℤ) := by
  classical
  exact if h : ∃ z : Rank → ℤ, F.harmonicOneProjection b = (H.point z).1 then
    some h.choose
  else none

/-- A successful coefficient recovery is exactly equality with the projected point. -/
theorem decodeCoefficients_eq_some_iff
    (H : HarmonicLatticePresentation I Rank) (b : F.C1) (z : Rank → ℤ) :
    H.decodeCoefficients b = some z ↔
      F.harmonicOneProjection b = (H.point z).1 := by
  classical
  unfold decodeCoefficients
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact h.choose_spec
    · intro hz
      apply H.point_injective
      apply Subtype.ext
      exact h.choose_spec.symm.trans hz
  · constructor
    · intro hnone
      cases hnone
    · intro hz
      exact (h ⟨z, hz⟩).elim

/-- Recovery fails precisely when the projected point is outside this presentation. -/
theorem decodeCoefficients_eq_none_iff
    (H : HarmonicLatticePresentation I Rank) (b : F.C1) :
    H.decodeCoefficients b = none ↔
      ¬ ∃ z : Rank → ℤ, F.harmonicOneProjection b = (H.point z).1 := by
  classical
  unfold decodeCoefficients
  split_ifs with h <;> simp_all

/-- The same integer message is recovered from an actual encrypted observation. -/
theorem decodeCoefficients_encrypt
    (H : HarmonicLatticePresentation I Rank)
    (z : Rank → ℤ) (opening : HodgeNoise F) :
    H.decodeCoefficients (H.encrypt z opening).observed = some z := by
  rw [H.decodeCoefficients_eq_some_iff]
  exact H.encrypt_projection_eq_point z opening

end HarmonicLatticePresentation

end HomotopicalEncryption.Sheaf.CellularSheaf
