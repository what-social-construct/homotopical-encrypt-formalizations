module

public import Helfer.Signature
public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy

@[expose] public section

/-!
# Homotopy equivalence of algebraic interpretations

The definitions below are the typed fragment of Helfer's Definition 7.1 used
by HCP. Function symbols commute up to right homotopy, and a homotopy
equivalence is componentwise a weak equivalence. On cofibrant-fibrant objects
in a model category this is precisely the homotopy-equivalence condition used
by Helfer.
-/

namespace Hcrypt.Helfer

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

universe u₁ u₂ v₁ v₂

variable
    {C : Type u₂} [Category.{v₂} C]
    [HasTerminal C] [HasBinaryProducts C] [ModelCategory C]
    {S : Signature.{u₁, v₁}}
    (M N : Interpretation C S)

/-- A homotopy homomorphism of interpretations (Helfer, Definition 7.1). -/
structure HomotopyHomomorphism where
  component : ∀ A, M.onSort A ⟶ N.onSort A
  preservesFunction : ∀ {Γ : List S.Sorts} {B : S.Sorts}
      (f : S.FunctionSymbol Γ B),
    RightHomotopyRel
      (M.onFunction f ≫ component B)
      (contextMap C component Γ ≫ N.onFunction f)

/--
A homotopy homomorphism between cofibrant-fibrant interpretations whose sort
components are weak equivalences. By the model-category Whitehead theorem,
these components are homotopy equivalences, matching Helfer's Definition 7.1.
-/
structure HomotopyEquivalence extends HomotopyHomomorphism M N where
  sourceFibrant : ∀ A, IsFibrant (M.onSort A)
  targetFibrant : ∀ A, IsFibrant (N.onSort A)
  sourceCofibrant : ∀ A, IsCofibrant (M.onSort A)
  targetCofibrant : ∀ A, IsCofibrant (N.onSort A)
  componentWeakEquivalence : ∀ A,
    WeakEquivalence (toHomotopyHomomorphism.component A)

/-- Two interpretations are connected by a Helfer homotopy equivalence. -/
def HomotopyEquivalent : Prop :=
  Nonempty (HomotopyEquivalence M N)

namespace HomotopyEquivalence

/--
Each component of a Helfer equivalence has an actual homotopy inverse. This is
the model-category Whitehead theorem applied using the cofibrant-fibrant data
carried by the interpretation equivalence.
-/
theorem component_hasHomotopyInverse
    (e : HomotopyEquivalence M N) (A : S.Sorts) :
    ∃ g : N.onSort A ⟶ M.onSort A,
      RightHomotopyRel (e.component A ≫ g) (𝟙 (M.onSort A)) ∧
      RightHomotopyRel (g ≫ e.component A) (𝟙 (N.onSort A)) := by
  letI : IsFibrant (M.onSort A) := e.sourceFibrant A
  letI : IsFibrant (N.onSort A) := e.targetFibrant A
  letI : IsCofibrant (M.onSort A) := e.sourceCofibrant A
  letI : IsCofibrant (N.onSort A) := e.targetCofibrant A
  letI : WeakEquivalence (e.component A) := e.componentWeakEquivalence A
  exact RightHomotopyClass.whitehead (e.component A)

end HomotopyEquivalence

end Hcrypt.Helfer
