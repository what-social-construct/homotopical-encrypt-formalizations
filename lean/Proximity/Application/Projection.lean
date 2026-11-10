module

public import Mathlib.Basic.Real.Basic

@[expose] public section

/-
  Generic proximity projection vocabulary.

  Paper correspondence:
  - Paper 1 Section 6: abstract lossy projection from sheaf/cochain data to
    code/evaluation shadows.
  - Paper 1 Section 5: projection begins only after the public artifact stack is
    fixed.

  This file is intentionally lightweight. It names the abstract projection from
  a sheaf-side received-word/cochain view to a code/evaluation shadow without
  importing heavier concrete axiom modules.

  Projection-local invariants that depend on the concrete math object live in
  the stage-specific files. The near/far gap question is intentionally deferred
  to `Proximity.Application.Problem`, where a completed projection chain can be calibrated
  as a promised decision problem.
-/

namespace Hcrypt
namespace Proximity

/--
A sheaf-side proximity instance.

`Cochain` is the received-word-like cellular datum. `GlobalSection` is the
exactly gluable/harmonic condition, and `disagreement` is the local obstruction
or syndrome size, e.g. a norm of `δ c` or a spectral/coboundary energy.
-/
structure SheafProximityInstance where
  Cochain : Type
  GlobalSection : Cochain → Prop
  disagreement : Cochain → ℝ

/--
A projected code/evaluation shadow of a sheaf proximity instance.

The structure is deliberately generic: the target may later be instantiated by
an evaluation code, a public commitment layer, or another finite shadow of the
sheaf stack.
-/
structure CodeShadow where
  Word : Type
  Codeword : Word → Prop
  distanceToCode : Word → ℝ

/--
Projection from sheaf-side cochains to a code/evaluation shadow.

The two core contracts are:
* exact global sections project to codewords;
* projected distance is controlled by sheaf-side disagreement.
-/
structure EvaluationProjection (S : SheafProximityInstance) (C : CodeShadow) where
  map : S.Cochain → C.Word
  preservesGlobalSections :
    ∀ c : S.Cochain, S.GlobalSection c → C.Codeword (map c)
  distanceControlled :
    ∀ c : S.Cochain, C.distanceToCode (map c) ≤ S.disagreement c

/-- The code shadow of an exact global section is a codeword. -/
theorem projected_global_section_is_codeword
    {S : SheafProximityInstance} {C : CodeShadow}
    (η : EvaluationProjection S C)
    (c : S.Cochain) :
    S.GlobalSection c → C.Codeword (η.map c) :=
  η.preservesGlobalSections c

/-- Projection does not exceed the declared sheaf-side disagreement budget. -/
theorem projected_distance_le_disagreement
    {S : SheafProximityInstance} {C : CodeShadow}
    (η : EvaluationProjection S C)
    (c : S.Cochain) :
    C.distanceToCode (η.map c) ≤ S.disagreement c :=
  η.distanceControlled c

/--
Near-global sheaf data projects to near-code data.

This is the lightweight theorem shape needed for later proximity comparisons:
if the sheaf-side disagreement is at most `ε`, then the projected shadow is
within `ε` of the target code/shadow.
-/
theorem projected_near_code_of_disagreement_le
    {S : SheafProximityInstance} {C : CodeShadow}
    (η : EvaluationProjection S C)
    {c : S.Cochain} {ε : ℝ}
    (h : S.disagreement c ≤ ε) :
    C.distanceToCode (η.map c) ≤ ε :=
  le_trans (η.distanceControlled c) h

/--
An optional list-size interface for projected shadows.

This keeps list/proximity questions available without asserting a particular
external theorem. An instantiation can define `nearbyCodewords w ε` using the
target metric and then ask for bounds on its cardinality.
-/
structure ListShadow (C : CodeShadow) where
  nearbyCodewords : C.Word → ℝ → Set C.Word
  nearbyAreCodewords :
    ∀ (w u : C.Word) (ε : ℝ), u ∈ nearbyCodewords w ε → C.Codeword u
  listBound : ℝ → ℕ → Prop

end Proximity
end Hcrypt
