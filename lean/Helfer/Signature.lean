module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

@[expose] public section

/-!
# Multi-sorted algebraic signatures and interpretations

This file formalizes the finite-product part of Joseph Helfer's Definition 6.1.
It deliberately stops before formula syntax and fibrational semantics: the HCP
hardness bridge only needs a typed interpretation and the homotopy-invariance
boundary supplied in `Helfer.Invariance`.
-/

namespace HomotopicalEncryption.Helfer

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

/-- A multi-sorted algebraic signature as in Helfer, Definition 6.1. -/
structure Signature where
  Sorts : Type u₁
  FunctionSymbol : List Sorts → Sorts → Type v₁

variable (C : Type u₂) [Category.{v₂} C]
  [HasTerminal C] [HasBinaryProducts C]

/-- The chosen finite product interpreting a list of sorts. -/
noncomputable def contextObject {S : Type u₁} (X : S → C) : List S → C
  | [] => ⊤_ C
  | A :: Γ => X A ⨯ contextObject X Γ

/-- The finite-product map induced componentwise by a family of arrows. -/
noncomputable def contextMap {S : Type u₁} {X Y : S → C}
    (α : ∀ A, X A ⟶ Y A) :
    (Γ : List S) → contextObject C X Γ ⟶ contextObject C Y Γ
  | [] => terminal.from _
  | A :: Γ => prod.map (α A) (contextMap α Γ)

/--
An interpretation of an algebraic signature in a category with finite
products. The canonical products supplied by the ambient category implement
the product choices appearing explicitly in Helfer's Definition 6.1.
-/
structure Interpretation (S : Signature) where
  onSort : S.Sorts → C
  onFunction : ∀ {Γ : List S.Sorts} {B : S.Sorts},
    S.FunctionSymbol Γ B → (contextObject C onSort Γ ⟶ onSort B)

end HomotopicalEncryption.Helfer
