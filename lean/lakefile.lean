import Lake
open Lake DSL


package «homotopical-encrypt-proofs» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

lean_lib Axioms where
  srcDir := "."
  roots := #[`Axioms.HelferFOL]

lean_lib CVP where
  srcDir := "."
  roots := #[`CVP]

lean_lib HCP where
  srcDir := "."
  roots := #[`HCP,
    `HCP.AxisFamily]

lean_lib Hardness where
  srcDir := "."
  roots := #[`Hardness]

lean_lib Helfer where
  srcDir := "."
  roots := #[`Helfer,
    `Helfer.CochainModel,
    `Helfer.HomotopyEquivalence,
    `Helfer.Invariance,
    `Helfer.Signature]

lean_lib Laplacian where
  srcDir := "."
  roots := #[`Laplacian.Grassmannian.SearchSpace,
    `Laplacian.Hodge,
    `Laplacian.Projection]

lean_lib Proximity where
  srcDir := "."
  roots := #[`Proximity.Application.Problem,
    `Proximity.Application.Projection,
    `Proximity.Concrete.Grassmannian,
    `Proximity.Concrete.GrassmannianPlucker,
    `Proximity.Concrete.GrassmannianPlucker.Concrete,
    `Proximity.Concrete.GrassmannianPlucker.Reconstruction]

lean_lib Sheaf where
  srcDir := "."
  roots := #[`Sheaf.CellComplex,
    `Sheaf.Cellular,
    `Sheaf.CoefficientRecovery,
    `Sheaf.Equivalence,
    `Sheaf.HCPAxisFamily,
    `Sheaf.HarmonicLattice,
    `Sheaf.Hodge,
    `Sheaf.Integral,
    `Sheaf.ObservationQuotient]

lean_lib TCB where
  srcDir := "."
  roots := #[`TCB.PluckerObservation]

@[default_target]
lean_lib Palomar where
  srcDir := "."
  roots := #[`Palomar.PaperOne.Solution]

lean_lib PalomarChallenge where
  srcDir := "."
  roots := #[`Palomar.PaperOne.Challenge]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"
