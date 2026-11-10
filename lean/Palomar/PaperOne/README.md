# Hidden Hodge targets and discrete closest vectors

This entry covers eight selected result groups from *Homotopical Encryption:
Hidden Hodge Operators and the Harmonic Cochain Problem*. It proves finite
Hodge decomposition and recovery, a discrete closest-vector comparison, and
actual cellular examples in which one public observation has different hidden
harmonic targets. It also records the limits of an exact-component observation
and recovery from full projective Plücker coordinates.

[Challenge](Challenge.lean) gives independent mathematical definitions using
Mathlib imports only. [Solution](Solution.lean) identifies those presentations
with the canonical project objects and reuses their proofs through explicit
adapters. [Comparator configuration](comparator.json) selects **46 theorems**:
**21 manuscript-facing declarations** and **25 supporting declarations**. These
are coverage counts, rather than a count of independent research results. There are no
definition holes. The two pure finite-product helpers
`Hcrypt.Helfer.contextObject` and `Hcrypt.Helfer.contextMap` are independently
restated under their canonical names in the Challenge. They retain their
ordinary categorical meanings.

In the crosswalk, `E` means `Hcrypt.Palomar.PaperOne`, `CS` means
`E.CellularSheaf`, `HB` means `E.HCPBridge`, `AF` means `E.AxisFamily`, and
`PL` means `E.Plucker`. The source labels refer to the
[versioned manuscript](../../../papers/paper1/main.tex).
Canonical names below belong to the implementation, outside the entry namespace.

| Group / manuscript source | Entry declarations and mathematical content | Canonical proof owners |
| --- | --- | --- |
| P1-S01 · §2.1 `prop:hodge-decomposition`; §3.3/appendix | `E.Hodge_Decomposition_Theorem`, `E.Hodge_Decomposition_unique`, `CS.HodgeEncryptedCochain.harmonicOneProjection_observed`, `CS.HarmonicLatticePresentation.decodeCoefficients_encrypt`: orthogonal decomposition with unique components and private recovery. | [Hardness](../../Hardness.lean), [Sheaf/Hodge](../../Sheaf/Hodge.lean), [Sheaf/CoefficientRecovery](../../Sheaf/CoefficientRecovery.lean); the latter two owners use namespace `Hcrypt.Sheaf.CellularSheaf`. |
| P1-S02 · §3.2 `prop:hcp-to-cvp` | `E.exists_matrix_ker_eq_range`, `E.Hodge_GeneratedSubspace_Reduction_Proof`: realize a field-linear image as a matrix kernel and obtain the stated image-membership consequence for a displayed-operator solver. | The same two unprefixed declaration names in [Hardness](../../Hardness.lean). This result concerns the linear image. |
| P1-S03 · §3.3 `prop:hodge-projection-is-cvp` | `E.squaredDistance_projection_decomposition`, `E.solution_iff_projectedTarget`: projection preserves exactly the discrete CVP answers when the supplied lattice lies in the projected subspace. | `HarmonicCVPBridge.squaredDistance_projection_decomposition` and `HarmonicCVPBridge.solution_iff_projectedTarget` in [Hardness](../../Hardness.lean). |
| P1-S04 · §3.3/appendix, cellular specialization | `E.concreteSheafHCP_CVP_solution_iff_message`, `E.concreteSheafHCP_CVP_existsUnique`: an actual encrypted cellular sample has the presented harmonic message as its unique discrete CVP answer. | The same unprefixed declaration names in [Hardness](../../Hardness.lean), using a supplied integral harmonic-lattice presentation. |
| P1-S05 · §3.4 `prop:cvp-insufficient`; §3.5 `prop:cellular-axis-ambiguity` | `HB.operativeTargets_ne_of_kernelSeparation`, both `HB.cvpOracle_insufficient_*` declarations, `AF.cellular_axis_ambiguity`, `AF.cvp_oracle_insufficient`: general conditional separation and its constructed cellular instance. | `Hcrypt.HCPBridge` in [Hardness](../../Hardness.lean); `Hcrypt.HCP.AxisFamily.shared_observation_distinct_nonzero_targets`, `cvp_oracle_insufficient` and the same-sample recovery facts in [HCP/AxisFamily](../../HCP/AxisFamily.lean). |
| P1-S06 · §3.5, weighted integral example | `AF.weighted_axis_recovery_obstruction`: coefficients two and one share the observation at `b=(1,2)`; one public coefficient decoder cannot recover both, while each private lattice has its own unique CVP answer. | `Hcrypt.HCP.AxisFamily.weighted_public_observations_eq`, `no_exact_encoded_message_decoder`, `weighted_cvp_solution_iff_operativeTarget`, `weighted_cvp_existsUnique` in [HCP/AxisFamily](../../HCP/AxisFamily.lean). |
| P1-B01 · §2 `prop:exact-component-obstruction` | `CS.HodgeEncryptedCochain.not_residual_norm_factors_exactComponent`, `not_far_preserving_exactComponent`: an allowed nonzero coexact direction prevents the full orthogonal residual from descending to the exact component. | Same terminal names under `Hcrypt.Sheaf.CellularSheaf.HodgeEncryptedCochain` in [ObservationQuotient](../../Sheaf/ObservationQuotient.lean). |
| P1-B02 · §6.2 `prop:plucker-recovery`; operative-observation appendix | `PL.recoverSubspace_frame`, `recoverHarmonicProjector_frame`, `recover_eq_operativeHarmonicComponent`: recover a frame's subspace and fixed-metric projector; identify the operative target when that subspace is the matrix kernel. | The first two names under `Hcrypt.Proximity.GrassmannianPlucker.Concrete` in [Reconstruction](../../Proximity/Concrete/GrassmannianPlucker/Reconstruction.lean); the last under `Hcrypt.TCB.PluckerObservation` in [PluckerObservation](../../TCB/PluckerObservation.lean). |

The Hodge statements retain the complex equation and the true cellular
degree-one operator. Coefficient recovery uses the supplied integral harmonic
lattice and is noncomputable. The discrete comparison retains an explicit
lattice, its inclusion in the harmonic subspace, and orthogonal projection.
The general ambiguity statements retain closed-test invariance, a kernel
separation witness, and the correct-oracle existence premise in the oracle
corollaries, with their stated uniform-solver quantifiers.

The constructed family uses actual cellular restriction maps and their Hodge
operators in the declared algebraic finite signed-incidence model. No regular
CW or simplicial realization of its base is asserted. Its public theory records the nonzero-cohomology tests in each
integer degree of the bounded-below real cochain model. Equality of that theory
is derived from the actual complexes. This formalizes the declared homological
fragment of Helfer's framework; full first-order semantics is outside this entry.
The Plücker carrier is the genuine exterior power modulo nonzero real scaling,
including the zero orbit; recovery for independent frames uses the full point
and the fixed Euclidean metric.

These results give exact mathematical recovery and observation obstructions.
They do not establish an asymptotic CVP-hardness reduction, distributional
encryption security, equality of larger released storage views, digest
inversion, an efficient decoder, or the manuscript's separate RS/MCA profile.
Novelty and priority are not asserted by this entry.

The independent Challenge and proved Solution build locally (**3,516/3,666
jobs**). Local Comparator passes statement/definition comparison and both
Lean and NanoDa kernel checks, permitting only `propext`, `Quot.sound` and
`Classical.choice`. This macOS diagnostic used `--inadvisably-no-sandbox`;
it is not protected preflight evidence. Protected Linux verification has
not run. The Challenge's **23 intentional theorem placeholders** are selected
comparison targets and are excluded from the Solution's zero proof-hole and
zero definition-hole counts.

A fresh `#print axioms` audit covers all **46** selected Solution declarations:
44 use exactly the three permitted axioms and two use subsets. The retained
implementation plus entry audit has **946 reports**; all 900 prior dependency
sets are unchanged. Declaration counts do not measure mathematical novelty.

From the repository's `lean/` project, the entry modules are
`Palomar.PaperOne.Challenge` and `Palomar.PaperOne.Solution`; its configuration is
`Palomar/PaperOne/comparator.json`. Comparator is bundled with the pinned Lean
4.35.0 toolchain. Protected comparison requires the supported Linux sandbox.
This directory records no completed protected preflight or registry submission.
[Metadata](formalization.yaml) records the source, scope and production account.
The repository and this entry use the [MIT licence](../../../LICENSE).
