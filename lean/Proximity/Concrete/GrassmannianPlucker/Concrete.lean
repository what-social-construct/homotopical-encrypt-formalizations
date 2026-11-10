module

public import Proximity.Concrete.GrassmannianPlucker

@[expose] public section

/-
  Concrete projective Plucker instantiation.

  Paper correspondence:
  - Paper 1 Section 6: concrete projective Plucker public-shadow surface.

  The raw coordinate is the actual exterior-power coordinate from
  `GrassmannianPlucker`. The public shadow is the projective quotient by
  nonzero scalar rescaling. This discharges the normalization/projective
  invariance part of the Plucker interface while keeping the two real
  exterior-algebra obligations explicit:

    * independent frames have nonzero exterior product;
    * two frame witnesses for the same Grassmannian point give projectively
      equivalent exterior coordinates.
-/

namespace Hcrypt
namespace Proximity
namespace GrassmannianPlucker
namespace Concrete

open scoped BigOperators Real Nat Classical Pointwise
open Matrix Real InnerProductSpace

set_option linter.mathlibStandardSet false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

variable {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

/-- Projective equivalence of exterior coordinates by nonzero scalar rescaling. -/
def ProjectivelyEquivalent
    (c d : ExteriorCoordinate n r) : Prop :=
  ∃ u : ℝˣ, d = (u : ℝ) • c

namespace ProjectivelyEquivalent

/-- Projective equivalence is reflexive. -/
theorem refl (c : ExteriorCoordinate n r) :
    ProjectivelyEquivalent c c := by
  refine ⟨1, ?_⟩
  simp

/-- Projective equivalence is symmetric. -/
theorem symm
    {c d : ExteriorCoordinate n r}
    (h : ProjectivelyEquivalent c d) :
    ProjectivelyEquivalent d c := by
  rcases h with ⟨u, rfl⟩
  refine ⟨u⁻¹, ?_⟩
  simp [smul_smul]

/-- Projective equivalence is transitive. -/
theorem trans
    {a b c : ExteriorCoordinate n r}
    (hab : ProjectivelyEquivalent a b)
    (hbc : ProjectivelyEquivalent b c) :
    ProjectivelyEquivalent a c := by
  rcases hab with ⟨u, rfl⟩
  rcases hbc with ⟨v, rfl⟩
  refine ⟨v * u, ?_⟩
  simp [smul_smul]

end ProjectivelyEquivalent

/-- Setoid identifying exterior coordinates up to nonzero scalar rescaling. -/
def projectiveSetoid (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) :
    Setoid (ExteriorCoordinate n r) where
  r := ProjectivelyEquivalent
  iseqv := by
    refine ⟨ProjectivelyEquivalent.refl, ?_, ?_⟩
    · intro c d h
      exact ProjectivelyEquivalent.symm h
    · intro a b c hab hbc
      exact ProjectivelyEquivalent.trans hab hbc

/-- Public projective Plucker shadow. -/
abbrev ProjectiveShadow (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) :=
  Quotient (projectiveSetoid n r)

/-- Normalize an exterior coordinate to its projective shadow. -/
def normalizeProjective
    (c : ExteriorCoordinate n r) :
    ProjectiveShadow n r :=
  Quot.mk _ c

/-- Projectively equivalent coordinates have the same public projective shadow. -/
theorem normalizeProjective_eq_of_projectivelyEquivalent
    {c d : ExteriorCoordinate n r}
    (h : ProjectivelyEquivalent c d) :
    normalizeProjective c = normalizeProjective d :=
  Quotient.sound h

/--
The unrestricted concrete projective Plucker system.

`SupportAdmissible` is intentionally unrestricted here: chart/support
restrictions belong to `Gates.PluckerMetricGate` or to a later chart-specific
system. The Plucker-relation predicate is the exterior-algebra image condition,
recorded as decomposability for now.
-/
def projectiveFramedSystem
    (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) :
    FramedSystem n r where
  Shadow := ProjectiveShadow n r
  normalize := normalizeProjective
  Nonzero := fun c => c ≠ 0
  PluckerRelations := fun c => FrameWitness.Decomposable c
  Normalized := fun _ => True
  SupportAdmissible := fun _ => True
  ProjectivelyEquivalent := ProjectivelyEquivalent

/--
The remaining exterior-algebra facts needed for the concrete projective
Plucker system to be sound.
-/
structure ProjectiveSoundInputs
    (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) : Prop where
  nonzero_toExterior :
    ∀ W : FrameWitness n r, W.toExterior ≠ 0
  samePoint_projectivelyEquivalent :
    ∀ W V : FrameWitness n r,
      W.point = V.point →
        ProjectivelyEquivalent W.toExterior V.toExterior

namespace ProjectiveSoundInputs

/-- Concrete projective soundness from the two remaining algebraic inputs. -/
def toSound
    (h : ProjectiveSoundInputs n r) :
    (projectiveFramedSystem n r).Sound where
  nonzero := h.nonzero_toExterior
  pluckerRelations := by
    intro W
    exact FrameWitness.toExterior_decomposable W
  valid_shadow := by
    intro W
    exact ⟨trivial, trivial⟩
  projective_frame_invariance := h.samePoint_projectivelyEquivalent
  projective_invariance := by
    intro c d hcd
    exact normalizeProjective_eq_of_projectivelyEquivalent hcd

/--
Every frame witness is a valid raw coordinate for the concrete projective
system once the remaining algebraic inputs are supplied.
-/
theorem validRawCoordinate
    (h : ProjectiveSoundInputs n r)
    (W : FrameWitness n r) :
    (projectiveFramedSystem n r).ValidRawCoordinate W :=
  FramedSystem.validRawCoordinate_of_sound h.toSound W

/--
Every frame witness has a valid public projective shadow for the concrete
projective system once the remaining algebraic inputs are supplied.
-/
theorem validShadow
    (h : ProjectiveSoundInputs n r)
    (W : FrameWitness n r) :
    (projectiveFramedSystem n r).ValidShadow W :=
  FramedSystem.validShadow_of_sound h.toSound W

end ProjectiveSoundInputs

end

end Concrete
end GrassmannianPlucker
end Proximity
end Hcrypt
