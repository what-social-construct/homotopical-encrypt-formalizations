# Hidden Hodge targets and discrete closest vectors

This entry formalizes six selected groups from *Homotopical Encryption:
Hidden Hodge Operators and the Harmonic Cochain Problem*, organized in
Sections 1–3: primitives, the HCP recovery problem, and comparison with the
closest-vector problem. The constructed integral cellular families give
concrete instances of the hidden-member recovery obstruction.
[Manuscript source](../../../papers/paper1/main.tex).

[Comparator configuration](comparator.json) selects **36 declarations**:
**16 manuscript-facing and 20 supporting**. [Challenge](Challenge.lean)
uses Mathlib only and independently defines the mathematical objects.
[Solution](Solution.lean) identifies them with canonical objects and reuses
their proofs; its local import closure contains **21 modules**. Challenge has
**18 intentional theorem placeholders**; Solution and all definitions have
no proof holes. The two finite-product helpers
`HomotopicalEncryption.Helfer.contextObject` and `contextMap` are restated
under their canonical names in Challenge.

In the crosswalk, `E` is `HomotopicalEncryption.Palomar.PaperOne`, `CS` is
`E.CellularSheaf`, `HB` is `E.HCPBridge`, and `AF` is `E.AxisFamily`.

| Group / manuscript source | Entry declarations and mathematical content | Canonical proof owners |
| --- | --- | --- |
| P1-S01 · `prop:hodge-decomposition`; private recovery | `E.Hodge_Decomposition_Theorem`, `E.Hodge_Decomposition_unique`, `CS.HodgeEncryptedCochain.harmonicOneProjection_observed`, `CS.HarmonicLatticePresentation.decodeCoefficients_encrypt`: orthogonal decomposition with unique components and private recovery. | [Hardness](../../Hardness.lean), [Sheaf/Hodge](../../Sheaf/Hodge.lean), [Sheaf/CoefficientRecovery](../../Sheaf/CoefficientRecovery.lean); the latter two owners use namespace `HomotopicalEncryption.Sheaf.CellularSheaf`. |
| P1-S02 · `prop:hcp-to-cvp` | `E.exists_matrix_ker_eq_range`, `E.Hodge_GeneratedSubspace_Reduction_Proof`: realize a field-linear image as a matrix kernel and obtain the stated image-membership consequence for a displayed-operator solver. | The same two unprefixed declaration names in [Hardness](../../Hardness.lean). This result concerns the linear image. |
| P1-S03 · `prop:hodge-projection-is-cvp` | `E.squaredDistance_projection_decomposition`, `E.solution_iff_projectedTarget`: projection preserves exactly the discrete CVP answers when the supplied lattice lies in the projected subspace. | `HarmonicCVPBridge.squaredDistance_projection_decomposition` and `HarmonicCVPBridge.solution_iff_projectedTarget` in [Hardness](../../Hardness.lean). |
| P1-S04 · cellular harmonic-lattice specialization | `E.concreteSheafHCP_CVP_solution_iff_message`, `E.concreteSheafHCP_CVP_existsUnique`: an actual encrypted cellular sample has the presented harmonic message as its unique discrete CVP answer. | The same unprefixed declaration names in [Hardness](../../Hardness.lean), using a supplied integral harmonic-lattice presentation. |
| P1-S05 · `prop:cvp-insufficient`, `prop:cellular-axis-ambiguity`, `cor:lattice-member-separation` | `HB.operativeTargets_ne_of_kernelSeparation`, both `HB.cvpOracle_insufficient_*` declarations, `AF.cellular_axis_ambiguity`, `AF.cvp_oracle_insufficient`: general conditional separation and its constructed cellular instance; the final corollary combines this group with P1-S04. | `HomotopicalEncryption.HCPBridge` in [Hardness](../../Hardness.lean); `HomotopicalEncryption.HCP.AxisFamily.shared_observation_distinct_nonzero_targets`, `cvp_oracle_insufficient`, and the derived `cvp_oracle_recovers_operative_component` / `cvp_known_member_hidden_member_separation` in [HCP/AxisFamily](../../HCP/AxisFamily.lean). |
| P1-S06 · weighted integral example | `AF.weighted_axis_recovery_obstruction`: coefficients two and one share the observation at `b=(1,2)`; one public coefficient decoder cannot recover both, while each private lattice has its own unique CVP answer. | `HomotopicalEncryption.HCP.AxisFamily.weighted_public_observations_eq`, `no_exact_encoded_message_decoder`, `weighted_cvp_solution_iff_operativeTarget`, `weighted_cvp_existsUnique` in [HCP/AxisFamily](../../HCP/AxisFamily.lean). |

The Hodge results retain the complex equation and actual adjoint Laplacian.
Discrete recovery uses a supplied integral harmonic-lattice presentation;
its coefficient decoder is noncomputable. The CVP bridge requires a supplied
lattice inside the harmonic subspace and preserves its discrete minimizers.

The generic ambiguity results require closed-test invariance and an explicit
kernel-separation witness; their oracle corollaries also retain the stated
correct-oracle existence premise. For the constructed cellular family, one
fixed correct rank-one oracle recovers the target when the operative lattice
is supplied. At the shared public observation, the same oracle cannot select
both distinct hidden targets. Every compatible family containing that pair
inherits this exact-information obstruction. This is not an asymptotic
complexity-hardness or distributional-security claim.

The optional `HomotopicalEncryption.HCPBridge.ReflectsHomotopyEquivalence`
property in [HCP](../../HCP.lean), together with invariance, identifies public
class equality and the existing class set with the declared typed homotopy class. The actual
`Fin 2` family proves that property despite its different embedded kernels.
This classifies admitted representatives, while the matrix-level projection
is constrained on realized operators. The semantic fragment uses
nonzero-cohomology tests in the bounded-below real cochain model.

The current 36-declaration entry passed its focused local build, statement
and definition comparison, and Lean/NanoDa replay. Exact verification scope
is recorded in [metadata](formalization.yaml). From `lean/`:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build Palomar.PaperOne.Challenge Palomar.PaperOne.Solution
LEAN_NUM_THREADS=1 lake comparator --config Palomar/PaperOne/comparator.json
```

Protected comparison requires the supported Linux sandbox. These commands
use the pinned Lean/Mathlib project. [MIT licence](../../../LICENSE).
