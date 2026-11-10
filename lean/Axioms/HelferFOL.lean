module

public import Mathlib.Topology.Connected.PathConnected
public import Helfer

@[expose] public section

/-
  Path semantics and public classifiers for hidden Hodge presentations.

  This module re-exports the typed `HomotopicalEncryption.Helfer` signature,
  interpretations and homotopy equivalences. It adds abstract path equality,
  dependent transport, public fibers and path-witnessed class membership.

  The interfaces are inspired by Joseph Helfer's "First-order homotopical
  logic":
  - equality via a path-space replacement of the diagonal: Section 2;
  - h=-fibration structure and its dependent logical operations: Definition 4.3;
  - homotopy invariance of formula interpretations, and of satisfaction for
    closed formulas: Theorem 12.3.

  General lifting, dependent-logical coherence and first-order invariance are
  recorded as explicit interface obligations, rather than proved here. The
  public classifiers and class witnesses below specialize the path setup to
  HCP: a path respecting the classifier yields equal public labels, while
  classifier equality alone need not supply a path witness.
-/

namespace HomotopicalEncryption
namespace Axioms

universe u v w

/-- Minimal path-space interface used for first-order equality semantics. -/
class HasPathSpace (A : Type u) where
  Path : A → A → Type u

/-- Axioms making the path-space interpretation an equivalence-style relation. -/
class PathAxioms (A : Type u) extends HasPathSpace A where
  refl : ∀ x : A, Path x x
  symm : ∀ {x y : A}, Path x y → Path y x
  trans : ∀ {x y z : A}, Path x y → Path y z → Path x z

/--
One concrete realization of the HFOL path object by a genuine continuous path
in a topological representative space.

This is intentionally an opt-in adapter rather than a global instance.  The
HFOL interface also admits categorical, simplicial, and isometric-groupoid path
witnesses that need not be literal interval-valued curves.
-/
abbrev HomotopyPath {A : Type u} [TopologicalSpace A] (x y : A) :=
  _root_.Path x y

/-- Mathlib continuous paths supply the reflexive/symmetric/transitive HFOL path operations. -/
noncomputable def topologicalPathAxioms
    (A : Type u) [TopologicalSpace A] : PathAxioms A where
  Path := fun x y => HomotopyPath x y
  refl := fun x => _root_.Path.refl x
  symm := fun p => p.symm
  trans := fun p q => p.trans q

/-- In the continuous realization, inhabited HFOL path equality is Mathlib's `Joined`. -/
abbrev ContinuouslyPathEquivalent {A : Type u} [TopologicalSpace A]
    (x y : A) : Prop :=
  Joined x y

/-- The diagonal statement: equality is interpreted by inhabited path-space. -/
def EqualityByPaths {A : Type u} [HasPathSpace A] (x y : A) : Prop :=
  Nonempty (HasPathSpace.Path x y)

theorem equalityByPaths_refl {A : Type u} [PathAxioms A] (x : A) :
  EqualityByPaths x x := by
  exact ⟨PathAxioms.refl x⟩

theorem equalityByPaths_symm {A : Type u} [PathAxioms A] {x y : A} :
  EqualityByPaths x y → EqualityByPaths y x := by
  intro hxy
  rcases hxy with ⟨p⟩
  exact ⟨PathAxioms.symm p⟩

theorem equalityByPaths_trans {A : Type u} [PathAxioms A] {x y z : A} :
  EqualityByPaths x y → EqualityByPaths y z → EqualityByPaths x z := by
  intro hxy hyz
  rcases hxy with ⟨p₁⟩
  rcases hyz with ⟨p₂⟩
  exact ⟨PathAxioms.trans p₁ p₂⟩

/-- Alias used when the path-space interpretation is treated as equivalence. -/
abbrev PathEquivalent {A : Type u} [HasPathSpace A] (x y : A) : Prop :=
  EqualityByPaths x y

/-- Path equivalence is reflexive under the path axioms. -/
theorem pathEquivalent_refl {A : Type u} [PathAxioms A] (x : A) :
    PathEquivalent x x :=
  equalityByPaths_refl x

/-- Path equivalence is symmetric under the path axioms. -/
theorem pathEquivalent_symm {A : Type u} [PathAxioms A] {x y : A} :
    PathEquivalent x y → PathEquivalent y x :=
  equalityByPaths_symm

/-- Path equivalence is transitive under the path axioms. -/
theorem pathEquivalent_trans {A : Type u} [PathAxioms A] {x y z : A} :
    PathEquivalent x y → PathEquivalent y z → PathEquivalent x z :=
  equalityByPaths_trans

/-- Public classifier/fingerprint map from hidden objects to public class data. -/
structure PublicClassifier (A : Type u) (P : Type v) where
  π : A → P

/--
Compatibility datum saying that a public classifier is obtained from a
fibration/base projection followed by a (possibly lossy) classifier on the
base.

At the level of objects this is the factorization `π = κ ∘ p` used in Paper 1,
Section 4.  The special case `κ = id` identifies the classifier with the base
projection, while the general case permits several base points to share one
public class value.
-/
structure PublicClassifierFactorization
    {A : Type u} {B : Type v} {P : Type w}
    (baseProjection : A → B) (C : PublicClassifier A P) where
  classifyBase : B → P
  factors : C.π = classifyBase ∘ baseProjection

/-- Fiber of the underlying base projection over one base point. -/
def BaseFiber {A : Type u} {B : Type v}
    (baseProjection : A → B) (b : B) : Set A :=
  { x | baseProjection x = b }

namespace PublicClassifierFactorization

/-- Classification of a hidden representative agrees with classification of its base point. -/
theorem classValue_eq_baseClass
    {A : Type u} {B : Type v} {P : Type w}
    {baseProjection : A → B} {C : PublicClassifier A P}
    (F : PublicClassifierFactorization baseProjection C) (x : A) :
    C.π x = F.classifyBase (baseProjection x) := by
  rw [F.factors]
  rfl

end PublicClassifierFactorization

/-- Two hidden objects have the same public class/fingerprint. -/
def SamePublicClass {A : Type u} {P : Type v}
    (C : PublicClassifier A P) (x y : A) : Prop :=
  C.π x = C.π y

/-- Hidden fiber over a public class/fingerprint value. -/
def PublicFiber {A : Type u} {P : Type v}
    (C : PublicClassifier A P) (p : P) : Set A :=
  { x | C.π x = p }

namespace PublicClassifierFactorization

/--
The public fiber over `α` is the union of all base fibers whose base points
are sent to `α`.
-/
theorem publicFiber_eq_iUnion_baseFibers
    {A : Type u} {B : Type v} {P : Type w}
    {baseProjection : A → B} {C : PublicClassifier A P}
    (F : PublicClassifierFactorization baseProjection C) (α : P) :
    PublicFiber C α =
      ⋃ b : { b : B // F.classifyBase b = α }, BaseFiber baseProjection b.1 := by
  ext x
  constructor
  · intro hx
    have hα : F.classifyBase (baseProjection x) = α := by
      rw [← F.classValue_eq_baseClass x]
      exact hx
    apply Set.mem_iUnion.2
    exact ⟨⟨baseProjection x, hα⟩, rfl⟩
  · intro hx
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hx
    change C.π x = α
    rw [F.classValue_eq_baseClass x, hb]
    exact b.property

end PublicClassifierFactorization

/-- Public class of a hidden representative. -/
def PublicClassOf {A : Type u} {P : Type v}
    (C : PublicClassifier A P) (x : A) : Set A :=
  PublicFiber C (C.π x)

/-- Every representative lies in its own public class. -/
theorem mem_publicClassOf_self {A : Type u} {P : Type v}
    (C : PublicClassifier A P) (x : A) :
    x ∈ PublicClassOf C x := by
  rfl

/-- Same-public-class is reflexive. -/
theorem samePublicClass_refl {A : Type u} {P : Type v}
    (C : PublicClassifier A P) (x : A) :
    SamePublicClass C x x := by
  rfl

/-- Same-public-class is symmetric. -/
theorem samePublicClass_symm {A : Type u} {P : Type v}
    {C : PublicClassifier A P} {x y : A} :
    SamePublicClass C x y → SamePublicClass C y x := by
  intro h
  exact h.symm

/-- Same-public-class is transitive. -/
theorem samePublicClass_trans {A : Type u} {P : Type v}
    {C : PublicClassifier A P} {x y z : A} :
    SamePublicClass C x y → SamePublicClass C y z → SamePublicClass C x z := by
  intro hxy hyz
  exact hxy.trans hyz

/-- Path equality respects the public classifier. -/
def PathRespectsPublicClass {A : Type u} {P : Type v} [HasPathSpace A]
    (C : PublicClassifier A P) : Prop :=
  ∀ {x y : A}, PathEquivalent x y → SamePublicClass C x y

/-- Hidden witness that a secret representative lies in a public class. -/
structure ClassMembershipWitness {A : Type u} {P : Type v} [HasPathSpace A]
    (C : PublicClassifier A P) (secret representative : A) where
  path : HasPathSpace.Path secret representative

/-- A class-membership witness entails path equality. -/
theorem classMembership_path {A : Type u} {P : Type v} [HasPathSpace A]
    {C : PublicClassifier A P} {secret representative : A}
    (w : ClassMembershipWitness C secret representative) :
    PathEquivalent secret representative := by
  exact ⟨w.path⟩

/-- A class-membership witness has a public shadow when paths preserve class data. -/
theorem classMembership_samePublicClass {A : Type u} {P : Type v} [HasPathSpace A]
    {C : PublicClassifier A P} (hC : PathRespectsPublicClass C)
    {secret representative : A}
    (w : ClassMembershipWitness C secret representative) :
    SamePublicClass C secret representative := by
  exact hC (classMembership_path w)

/-- The public classifier is non-faithful when one public class has distinct hidden representatives. -/
def PublicClassifierNonFaithful {A : Type u} {P : Type v}
    (C : PublicClassifier A P) : Prop :=
  ∃ x y : A, x ≠ y ∧ SamePublicClass C x y

/-- Non-faithfulness gives a nontrivial public fiber. -/
theorem nonFaithful_has_nontrivial_fiber {A : Type u} {P : Type v}
    {C : PublicClassifier A P}
    (h : PublicClassifierNonFaithful C) :
    ∃ p : P, ∃ x y : A, x ∈ PublicFiber C p ∧ y ∈ PublicFiber C p ∧ x ≠ y := by
  rcases h with ⟨x, y, hxy, hpub⟩
  exact ⟨C.π x, x, y, rfl, hpub.symm, hxy⟩

/-- Minimal dependent transport primitive along hidden paths. -/
class HasPathTransport {A : Type u} [HasPathSpace A] (F : A → Type v) where
  transport : ∀ {x y : A}, HasPathSpace.Path x y → F x → F y

/-- Interface-level obligations extracted from Helfer-style semantics. -/
structure HelferFOL where
  /-- Equality/diagonal semantics is path-space based (not strict boolean equality). -/
  DiagonalPathSemantics : Prop
  /-- Fibration/cartesian-lift style transport principle is available. -/
  CartesianLiftingPrinciple : Prop
  /-- Σ/Π dependent behavior is coherent with encryption/decryption contracts. -/
  SigmaPiCoherent : Prop
  /-- Homotopy-equivalent structures satisfy the same first-order theory. -/
  HomotopyInvarianceFO : Prop
  /-- Equivalence-class witness discipline (class membership has witness semantics). -/
  ClassWitnessSound : Prop

abbrev HelferFOLWellFormed (H : HelferFOL) : Prop :=
  H.DiagonalPathSemantics
  ∧ H.CartesianLiftingPrinciple
  ∧ H.SigmaPiCoherent
  ∧ H.HomotopyInvarianceFO
  ∧ H.ClassWitnessSound

end Axioms
end HomotopicalEncryption
