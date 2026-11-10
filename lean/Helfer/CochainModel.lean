module

public import Helfer.Invariance
public import Sheaf.Equivalence
public import Mathlib.Algebra.Homology.ModelCategory.Injective
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

@[expose] public section

/-!
# A genuine cochain model for a homological Helfer fragment

The ambient model category is Mathlib's injective Quillen model structure on
bounded-below real-module cochain complexes.  Its weak equivalences are actual
quasi-isomorphisms.  The closed tests below ask whether cohomology in a named
degree is nonzero.  Their invariance is proved for every typed interpretation;
this explicit homological fragment does not assert Helfer's full first-order
fibrational semantics or his general Theorem 12.3.

The cellular adapter retains the actual two coboundaries.  Strict chain
isomorphisms, including degreewise isometric cellular equivalences, give the
typed Helfer equivalences used by HCP.  No public encoding or cryptographic
indistinguishability statement is selected here.
-/

set_option autoImplicit false

noncomputable section

namespace Hcrypt.Helfer.CochainModel

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ZeroObject
open scoped CochainComplex.Plus.modelCategoryQuillen

/-- The actual Quillen model category of bounded-below real cochain complexes. -/
abbrev Model := CochainComplex.Plus (ModuleCat.{0} ℝ)

/-- The bounded-below property contains the actual zero complex. -/
instance boundedContainsZero : (CochainComplex.plus (ModuleCat.{0} ℝ)).ContainsZero where
  exists_zero := by
    refine ⟨HomologicalComplex.zero, HomologicalComplex.isZero_zero, 0, ?_⟩
    apply (CochainComplex.isStrictlyGE_iff _ 0).2
    intro i _hi
    exact isZero_zero (ModuleCat.{0} ℝ)

/-- A three-term real complex, with its actual square-zero law. -/
structure Data where
  C0 : ModuleCat.{0} ℝ
  C1 : ModuleCat.{0} ℝ
  C2 : ModuleCat.{0} ℝ
  d0 : C0 ⟶ C1
  d1 : C1 ⟶ C2
  squareZero : d0 ≫ d1 = 0

namespace Data

/-- The three given carriers, extended by the zero object in other degrees. -/
def term (D : Data) (i : ℤ) : ModuleCat ℝ :=
  if i = 0 then D.C0 else if i = 1 then D.C1 else if i = 2 then D.C2 else 0

/-- The given differentials, extended by zero. -/
def differential (D : Data) (i : ℤ) : D.term i ⟶ D.term (i + 1) := by
  by_cases h0 : i = 0
  · subst i
    exact D.d0
  by_cases h1 : i = 1
  · subst i
    exact D.d1
  exact 0

theorem differential_comp (D : Data) (i : ℤ) :
    D.differential i ≫ D.differential (i + 1) = 0 := by
  by_cases h0 : i = 0
  · subst i
    change D.d0 ≫ D.d1 = 0
    exact D.squareZero
  by_cases h1 : i = 1
  · subst i
    change D.d1 ≫ (0 : D.C2 ⟶ D.term 3) = 0
    simp
  simp [differential, h0, h1]

/-- The actual integer-indexed complex with the supplied two differentials. -/
def complex (D : Data) : CochainComplex (ModuleCat ℝ) ℤ :=
  CochainComplex.of D.term D.differential D.differential_comp

@[simp]
theorem complex_X (D : Data) (i : ℤ) : D.complex.X i = D.term i := rfl

@[simp]
theorem complex_d01 (D : Data) : D.complex.d 0 1 = D.d0 := by
  change D.differential 0 = D.d0
  rfl

@[simp]
theorem complex_d12 (D : Data) : D.complex.d 1 2 = D.d1 := by
  change D.differential 1 = D.d1
  rfl

theorem strictlyGE (D : Data) : D.complex.IsStrictlyGE 0 := by
  apply (CochainComplex.isStrictlyGE_iff D.complex 0).2
  intro i hi
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have h2 : i ≠ 2 := by omega
  simpa [complex, term, h0, h1, h2] using isZero_zero (ModuleCat ℝ)

/-- The same complex, now an object of the genuine bounded-below model category. -/
def model (D : Data) : Model := ⟨D.complex, 0, D.strictlyGE⟩

/-- A strict chain isomorphism, retaining the three actual component isomorphisms. -/
structure StrictIso (D E : Data) where
  degreeZero : D.C0 ≅ E.C0
  degreeOne : D.C1 ≅ E.C1
  degreeTwo : D.C2 ≅ E.C2
  commutesZero : degreeZero.hom ≫ E.d0 = D.d0 ≫ degreeOne.hom
  commutesOne : degreeOne.hom ≫ E.d1 = D.d1 ≫ degreeTwo.hom

namespace StrictIso

variable {D E : Data}

/-- Extend the actual degreewise isomorphisms by the identity of zero objects. -/
def termIso (e : StrictIso D E) (i : ℤ) : D.term i ≅ E.term i := by
  by_cases h0 : i = 0
  · subst i
    exact e.degreeZero
  by_cases h1 : i = 1
  · subst i
    exact e.degreeOne
  by_cases h2 : i = 2
  · subst i
    exact e.degreeTwo
  simpa [term, h0, h1, h2] using Iso.refl (0 : ModuleCat ℝ)

theorem termIso_commutes (e : StrictIso D E) (i : ℤ) :
    (e.termIso i).hom ≫ E.differential i =
      D.differential i ≫ (e.termIso (i + 1)).hom := by
  by_cases h0 : i = 0
  · subst i
    change e.degreeZero.hom ≫ E.d0 = D.d0 ≫ e.degreeOne.hom
    exact e.commutesZero
  by_cases h1 : i = 1
  · subst i
    change e.degreeOne.hom ≫ E.d1 = D.d1 ≫ e.degreeTwo.hom
    exact e.commutesOne
  simp [differential, h0, h1]

/-- The resulting genuine isomorphism of integer-indexed complexes. -/
def complexIso (e : StrictIso D E) : D.complex ≅ E.complex :=
  HomologicalComplex.Hom.isoOfComponents e.termIso (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    simpa [complex] using e.termIso_commutes i)

/-- The same strict isomorphism in the bounded-below model category. -/
def modelIso (e : StrictIso D E) : D.model ≅ E.model :=
  (CochainComplex.plus (ModuleCat ℝ)).isoMk e.complexIso

end StrictIso

end Data

/-- Every real vector space is injective, proved using semisimplicity of the field. -/
theorem module_injective (M : ModuleCat ℝ) : CategoryTheory.Injective M := by
  let : Module.Injective ℝ M := Module.injective_of_isSemisimpleRing ℝ M
  exact Module.injective_object_of_injective_module ℝ M

/-- All bounded-below real complexes are fibrant in the injective model structure. -/
theorem model_isFibrant (K : Model) : IsFibrant K := by
  apply (CochainComplex.Plus.modelCategoryQuillen.isFibrant_iff K).2
  intro i
  exact module_injective _

/-- All objects are cofibrant because cofibrations are monomorphisms. -/
theorem model_isCofibrant (K : Model) : IsCofibrant K := by
  change Cofibration (initial.to K)
  apply (CochainComplex.Plus.modelCategoryQuillen.cofibration_iff _).2
  exact ((isZero_zero Model).of_iso HasZeroObject.zeroIsoInitial.symm).mono _

/-- One complex sort; its differential and homology live in the model object. -/
def signature : Signature.{0, 0} where
  Sorts := Unit
  FunctionSymbol _ _ := PEmpty

/-- Interpret the sole sort by the actual complex. -/
def interpretation (K : Model) : Interpretation Model signature where
  onSort _ := K
  onFunction := fun f => nomatch f

/-- Explicit homological closed tests: nonzero cohomology in a named degree. -/
def semantics : ClosedSemantics (C := Model) signature where
  ClosedFormula := ℤ
  Satisfies M i := ¬ IsZero ((M.onSort ()).obj.homology i)

/-- A genuine quasi-isomorphism gives an isomorphism of each tested homology object. -/
def homologyIso {K L : Model} (f : K ⟶ L) [WeakEquivalence f] (i : ℤ) :
    K.obj.homology i ≅ L.obj.homology i := by
  letI : _root_.QuasiIso f.hom :=
    (CochainComplex.Plus.modelCategoryQuillen.weakEquivalence_iff f).1 inferInstance
  exact _root_.isoOfQuasiIsoAt f.hom i

/-- The selected fragment is invariant for all interpretations, not just cellular examples. -/
theorem closedTestInvariance : ClosedFormulaInvariance semantics := by
  constructor
  intro M N hMN i
  obtain ⟨e⟩ := hMN
  let : WeakEquivalence (e.component ()) := e.componentWeakEquivalence ()
  exact not_congr (homologyIso (e.component ()) i).isZero_iff

/-- The degree-one nontriviality test used by the HCP realization. -/
def nontrivialH1 (K : Model) : Prop :=
  semantics.Satisfies (interpretation K) (1 : ℤ)

/-- A strict isomorphism supplies all actual bifibrant and weak-equivalence data. -/
def homotopyEquivalence_of_iso {K L : Model} (e : K ≅ L) :
    HomotopyEquivalence (interpretation K) (interpretation L) where
  component _ := e.hom
  preservesFunction := by intro Γ B f; cases f
  sourceFibrant _ := model_isFibrant K
  targetFibrant _ := model_isFibrant L
  sourceCofibrant _ := model_isCofibrant K
  targetCofibrant _ := model_isCofibrant L
  componentWeakEquivalence _ := by
    apply (CochainComplex.Plus.modelCategoryQuillen.weakEquivalence_iff e.hom).2
    infer_instance

theorem equivalent_of_iso {K L : Model} (e : K ≅ L) :
    HomotopyEquivalent (interpretation K) (interpretation L) :=
  ⟨homotopyEquivalence_of_iso e⟩

theorem equivalent_refl (K : Model) :
    HomotopyEquivalent (interpretation K) (interpretation K) :=
  equivalent_of_iso (Iso.refl K)

/-- A supplied strict three-term isomorphism gives a typed Helfer equivalence. -/
theorem Data.StrictIso.equivalent {D E : Data} (e : Data.StrictIso D E) :
    HomotopyEquivalent (interpretation D.model) (interpretation E.model) :=
  equivalent_of_iso e.modelIso

section Cellular

open Sheaf CellularSheaf

variable {Vertex Edge Face : Type}
  [Fintype Vertex] [Fintype Edge] [Fintype Face]
  {X : OrientedTwoComplex Vertex Edge Face}

/-- The actual cellular complex data; square-zero is the existing cellular theorem. -/
def ofSheaf (F : CellularSheaf X) : Data where
  C0 := ModuleCat.of ℝ F.C0
  C1 := ModuleCat.of ℝ F.C1
  C2 := ModuleCat.of ℝ F.C2
  d0 := ModuleCat.ofHom F.delta0
  d1 := ModuleCat.ofHom F.delta1
  squareZero := by
    apply ModuleCat.hom_ext
    exact F.delta1_comp_delta0

/-- Actual degreewise isometric cellular maps induce a strict complex isomorphism. -/
def strictIso_of_isometricCochainEquiv {F G : CellularSheaf X}
    (e : IsometricCochainEquiv F G) : Data.StrictIso (ofSheaf F) (ofSheaf G) where
  degreeZero := e.degreeZero.toLinearEquiv.toModuleIso
  degreeOne := e.degreeOne.toLinearEquiv.toModuleIso
  degreeTwo := e.degreeTwo.toLinearEquiv.toModuleIso
  commutesZero := by
    apply ModuleCat.hom_ext
    exact e.delta0_commutes.symm
  commutesOne := by
    apply ModuleCat.hom_ext
    exact e.delta1_commutes.symm

/-- The cellular isometry realizes the actual typed Helfer equivalence. -/
theorem equivalent_of_isometricCochainEquiv {F G : CellularSheaf X}
    (e : IsometricCochainEquiv F G) :
    HomotopyEquivalent (interpretation (ofSheaf F).model)
      (interpretation (ofSheaf G).model) :=
  (strictIso_of_isometricCochainEquiv e).equivalent

end Cellular

end Hcrypt.Helfer.CochainModel
