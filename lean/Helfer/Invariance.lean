module

public import Helfer.HomotopyEquivalence

@[expose] public section

/-!
# Closed-formula homotopy-invariance boundary

Helfer's Theorem 12.3 is an external cited theorem. This module does not hide
that dependency behind an unproved Lean axiom: it packages the exact
closed-formula consequence as an explicit hypothesis that downstream HCP
theorems must receive.
-/

namespace HomotopicalEncryption.Helfer

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u₁ u₂ v₁ v₂ w

variable
    (C : Type u₂) [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C]
    {S : Signature.{u₁, v₁}}

/-- Closed-formula satisfaction attached to interpretations of one signature. -/
structure ClosedSemantics (S : Signature.{u₁, v₁}) where
  ClosedFormula : Type w
  Satisfies : Interpretation C S → ClosedFormula → Prop

variable {C} (sem : ClosedSemantics (C := C) S)

/-- The set of closed formulas satisfied by an interpretation. -/
def ClosedTheory (M : Interpretation C S) : Set sem.ClosedFormula :=
  { φ | sem.Satisfies M φ }

/-- Explicit closed-formula consequence of Helfer's Theorem 12.3. -/
structure ClosedFormulaInvariance [ModelCategory C] : Prop where
  theorem12_3_closed : ∀ {M N : Interpretation C S},
    HomotopyEquivalent M N →
      ∀ φ, sem.Satisfies M φ ↔ sem.Satisfies N φ

/-- Homotopy-equivalent interpretations have the same closed theory. -/
theorem closedTheory_eq [ModelCategory C]
    (hInv : ClosedFormulaInvariance sem) {M N : Interpretation C S}
    (hMN : HomotopyEquivalent M N) :
    ClosedTheory sem M = ClosedTheory sem N := by
  ext φ
  exact hInv.theorem12_3_closed hMN φ

end HomotopicalEncryption.Helfer
