module

public import Proximity.Concrete.GrassmannianPlucker.Concrete
public import Mathlib.Analysis.InnerProductSpace.ExteriorPower

@[expose] public section

/-!
# Recovering the harmonic subspace from its full projective Plucker point

The annihilator of exterior multiplication reconstructs the span of an
independent frame. It is invariant under nonzero rescaling and therefore
descends to the existing projective quotient. No digest inversion or
computational hiding claim is involved.
-/

set_option autoImplicit false

noncomputable section

namespace Hcrypt.Proximity.GrassmannianPlucker.Concrete

open scoped RealInnerProductSpace

section ExteriorFacts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {r : ℕ}

/-- An independent real frame has a nonzero actual exterior coordinate. -/
theorem exteriorCoordinate_ne_zero {frame : Fin r → E}
    (hframe : LinearIndependent ℝ frame) :
    exteriorPower.ιMulti ℝ r frame ≠ 0 := by
  intro hzero
  have hdet := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hframe
  apply hdet
  rw [← exteriorPower.inner_ιMulti_self frame, hzero]
  simp

/-- The same nonvanishing fact in the ambient exterior algebra. -/
theorem exteriorProduct_ne_zero {frame : Fin r → E}
    (hframe : LinearIndependent ℝ frame) :
    ExteriorAlgebra.ιMulti ℝ r frame ≠ 0 := by
  intro hzero
  apply exteriorCoordinate_ne_zero hframe
  apply Subtype.ext
  exact hzero

/-- Exterior multiplication by the frame detects precisely its linear span. -/
theorem mul_exteriorProduct_eq_zero_iff_mem_span
    {frame : Fin r → E} (hframe : LinearIndependent ℝ frame) (x : E) :
    ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ιMulti ℝ r frame = 0 ↔
      x ∈ Submodule.span ℝ (Set.range frame) := by
  have hcons : ExteriorAlgebra.ιMulti ℝ (r + 1) (Fin.cons x frame) =
      ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ιMulti ℝ r frame := by
    simp [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  rw [← hcons]
  constructor
  · intro hzero
    by_contra hnot
    exact exteriorProduct_ne_zero (hframe.finCons hnot) hzero
  · intro hmem
    apply (ExteriorAlgebra.ιMulti ℝ (r + 1)).map_linearDependent
    intro hindependent
    exact (linearIndependent_finCons.mp hindependent).2 hmem

end ExteriorFacts

variable {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

/-- The linear annihilator of left exterior multiplication by a coordinate. -/
def wedgeAnnihilator (c : ExteriorCoordinate n r) :
    Submodule ℝ (EuclideanSpace ℝ n) :=
  LinearMap.ker ((LinearMap.mulRight ℝ (c : ExteriorAlgebra ℝ (EuclideanSpace ℝ n))).comp
    (ExteriorAlgebra.ι ℝ))

omit [DecidableEq n] in
theorem mem_wedgeAnnihilator_iff (c : ExteriorCoordinate n r)
    (x : EuclideanSpace ℝ n) :
    x ∈ wedgeAnnihilator c ↔
      ExteriorAlgebra.ι ℝ x * (c : ExteriorAlgebra ℝ (EuclideanSpace ℝ n)) = 0 :=
  Iff.rfl

omit [DecidableEq n] in
/-- Nonzero coordinate rescaling leaves the recovered subspace unchanged. -/
theorem wedgeAnnihilator_eq_of_projectivelyEquivalent
    {c d : ExteriorCoordinate n r} (h : ProjectivelyEquivalent c d) :
    wedgeAnnihilator c = wedgeAnnihilator d := by
  rcases h with ⟨u, rfl⟩
  ext x
  simp only [mem_wedgeAnnihilator_iff, Submodule.coe_smul, mul_smul_comm]
  simp only [smul_eq_zero, Units.ne_zero, false_or]

/-- Recover a linear subspace from the existing full projective quotient. -/
def recoverSubspace (shadow : ProjectiveShadow n r) :
    Submodule ℝ (EuclideanSpace ℝ n) :=
  Quotient.lift wedgeAnnihilator
    (fun _ _ h => wedgeAnnihilator_eq_of_projectivelyEquivalent h) shadow

@[simp] theorem recoverSubspace_normalizeProjective (c : ExteriorCoordinate n r) :
    recoverSubspace (normalizeProjective c) = wedgeAnnihilator c := rfl

/-- The unrestricted quotient still contains the zero orbit; it decodes to top. -/
@[simp] theorem recoverSubspace_zero :
    recoverSubspace (normalizeProjective (0 : ExteriorCoordinate n r)) = ⊤ := by
  ext x
  simp [recoverSubspace_normalizeProjective, mem_wedgeAnnihilator_iff]

/-- Reconstruction returns the original operative harmonic subspace. -/
@[simp] theorem recoverSubspace_frame (W : FrameWitness n r) :
    recoverSubspace (normalizeProjective W.toExterior) = W.point.carrier := by
  rw [recoverSubspace_normalizeProjective, ← W.spans_submodule]
  ext x
  exact mul_exteriorProduct_eq_zero_iff_mem_span W.independent x

/-- At the fixed ambient metric the full point determines its harmonic projector. -/
def recoverHarmonicProjector (shadow : ProjectiveShadow n r) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
  (recoverSubspace shadow).starProjection

@[simp] theorem recoverHarmonicProjector_frame (W : FrameWitness n r) :
    recoverHarmonicProjector (normalizeProjective W.toExterior) =
      W.point.carrier.starProjection := by
  unfold recoverHarmonicProjector
  simp only [recoverSubspace_frame]

/-- The concrete independent-frame construction needs no extra nonzero premise. -/
theorem frame_toExterior_ne_zero (W : FrameWitness n r) : W.toExterior ≠ 0 :=
  exteriorCoordinate_ne_zero W.independent

/-- Two bases of the same operative subspace differ by a nonzero exterior scale. -/
theorem projectivelyEquivalent_of_same_point
    (W V : FrameWitness n r) (hpoint : W.point = V.point) :
    ProjectivelyEquivalent W.toExterior V.toExterior := by
  let f : Fin r → W.point.carrier := fun i => ⟨W.frame i, W.frame_mem i⟩
  let g : Fin r → W.point.carrier := fun i =>
    ⟨V.frame i, by rw [hpoint]; exact V.frame_mem i⟩
  have hf : LinearIndependent ℝ f :=
    LinearIndependent.of_comp W.point.carrier.subtype W.independent
  have hg : LinearIndependent ℝ g :=
    LinearIndependent.of_comp W.point.carrier.subtype V.independent
  have hdim : Module.finrank ℝ (⋀[ℝ]^r W.point.carrier) = 1 := by
    rw [exteriorPower.finrank_eq, W.point.rank_eq, Nat.choose_self]
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
    hdim (exteriorCoordinate_ne_zero hf) (exteriorPower.ιMulti ℝ r g)
  have hane : a ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at ha
    exact exteriorCoordinate_ne_zero hg ha.symm
  refine ⟨Units.mk0 a hane, ?_⟩
  have hambient := congrArg (exteriorPower.map r W.point.carrier.subtype) ha
  simpa [FrameWitness.toExterior, f, g, Function.comp_def] using hambient.symm

/-- Both formerly supplied exterior-algebra soundness inputs are constructed. -/
theorem projectiveSoundInputs (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) :
    ProjectiveSoundInputs n r where
  nonzero_toExterior := frame_toExterior_ne_zero
  samePoint_projectivelyEquivalent := projectivelyEquivalent_of_same_point

/-- The existing concrete framed system is sound without extra algebraic inputs. -/
theorem projectiveFramedSystem_sound : (projectiveFramedSystem n r).Sound :=
  (projectiveSoundInputs n r).toSound

/-- Equal full projective shadows recover the same operative carrier. -/
theorem carrier_eq_of_publicShadow_eq {W V : FrameWitness n r}
    (hshadow : (projectiveFramedSystem n r).publicShadow W =
      (projectiveFramedSystem n r).publicShadow V) :
    W.point.carrier = V.point.carrier := by
  have h := congrArg recoverSubspace hshadow
  simpa only [FramedSystem.publicShadow, projectiveFramedSystem,
    recoverSubspace_frame] using h

private theorem point_eq_of_carrier_eq {W V : HarmonicSubspace n r}
    (h : W.carrier = V.carrier) : W = V := by
  cases W
  cases V
  cases h
  rfl

/-- Full projective data identifies the ranked harmonic point exactly. -/
theorem publicShadow_eq_iff_same_point (W V : FrameWitness n r) :
    (projectiveFramedSystem n r).publicShadow W =
      (projectiveFramedSystem n r).publicShadow V ↔ W.point = V.point := by
  constructor
  · intro h
    exact point_eq_of_carrier_eq (carrier_eq_of_publicShadow_eq h)
  · intro h
    exact FramedSystem.publicShadow_eq_of_same_point projectiveFramedSystem_sound h

/-- The harmonic projector is fixed by the full projective point and ambient metric. -/
theorem harmonicProjector_eq_of_publicShadow_eq {W V : FrameWitness n r}
    (hshadow : (projectiveFramedSystem n r).publicShadow W =
      (projectiveFramedSystem n r).publicShadow V) :
    W.point.carrier.starProjection = V.point.carrier.starProjection := by
  rw [carrier_eq_of_publicShadow_eq hshadow]

/-- The normalized projection-model Laplacian is fixed by the full point. -/
theorem toLaplacian_eq_of_publicShadow_eq {W V : FrameWitness n r}
    (hshadow : (projectiveFramedSystem n r).publicShadow W =
      (projectiveFramedSystem n r).publicShadow V) :
    W.point.toLaplacian = V.point.toLaplacian := by
  rw [(publicShadow_eq_iff_same_point W V).mp hshadow]

end Hcrypt.Proximity.GrassmannianPlucker.Concrete
