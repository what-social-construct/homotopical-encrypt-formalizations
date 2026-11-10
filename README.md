# Hidden Hodge targets and discrete closest vectors

This local release candidate contains one selected formalization entry and its
actual Lean proof/import closure. Its [scope and statement crosswalk](lean/Palomar/PaperOne/README.md)
and [metadata](lean/Palomar/PaperOne/formalization.yaml) state the hypotheses and limitations.
The [configuration](lean/Palomar/PaperOne/comparator.json) selects **46 declarations**:
21 manuscript-facing and 25 supporting. These are coverage counts.

The manuscript program retains its recorded three-paper split:

| Paper | Owns |
|---|---|
| 1 | HCP foundations, hidden Hodge operators, harmonic recovery and CVP comparisons. |
| 2 | Protocol, cochains/commitments, storage, verification evidence and accepted transitions. |
| 3 | Proximity, Reed–Solomon bounds and quantitative metric comparisons using the shared objects. |

Paper 2 remains a working draft and is not included in this entry package.
Paper 3's core and bridge configurations are two verification entries for one
manuscript; they do not introduce another paper split.

Paper 1 is being prepared as the first public release. This package contains only its selected formalization and corresponding manuscript; the other papers remain outside this release.

The canonical [manuscript PDF](papers/paper1/main.pdf) and [TeX source](papers/paper1/main.tex)
are unchanged contextual evidence. The selected formalization covers the stated
groups, rather than every claim or future direction in the full manuscript.

The upstream development repository is currently private. Immutable upstream
URLs in the unchanged metadata record provenance; use the bundled manuscript
and local crosswalk for review navigation.

The source checkpoint is `13542370576d36de7251ae71b36807dec97bc0ae`. The package contains 31
local Lean modules: Challenge's closure has 1, Solution's has
30. The files retain their original module paths and source bytes.
The generated Lake file defaults to the selected Solution; Challenge is a
separate explicit build. No other paper's entry, plans, archives, runtime or
dependency/build caches are included. [MIT licence](LICENSE).

From `lean/`, reproduce the entry checks with the pinned toolchain:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build Palomar.PaperOne.Challenge
LEAN_NUM_THREADS=1 lake build
LEAN_NUM_THREADS=1 lake comparator --config Palomar/PaperOne/comparator.json
```

The last command requires the supported Linux sandbox. The development entry
passed local macOS comparison and Lean/NanoDa replay; that diagnostic disabled
the Linux sandbox. **This slim package has not yet passed protected preflight.**
Packaging/static checks do not substitute for a clean build, definition
comparison, dependency audit or kernel replay on these exact packaged inputs.

The [manual-only preflight workflow](.github/workflows/palomar-preflight.yml)
pins verifier pipeline `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` and selects this entry at `github.sha`.
It is prepared for a separately authorized immutable public release; the local
exporter performs no push, upload, workflow dispatch or registry submission.

[Packaging manifest](PALOMAR_PACKAGE_MANIFEST.json) records exact source copies, generated files,
README navigation rewrites, source-input hashes and selected-input changes
relative to the source checkpoint. The copied metadata's development validation
record is historical evidence, rather than a protected result for this package.
