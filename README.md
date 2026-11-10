# Hidden Hodge targets and discrete closest vectors

This package contains one selected Lean formalization and its manuscript.
The [statement crosswalk](lean/Palomar/PaperOne/README.md) describes the mathematical
claims, hypotheses and canonical proof owners. The [configuration](lean/Palomar/PaperOne/comparator.json)
selects 36 declarations: 16 main and 20 supporting.

Read the [manuscript PDF](papers/paper1/main.pdf), its [TeX source](papers/paper1/main.tex)
and the [formalization metadata](lean/Palomar/PaperOne/formalization.yaml).
Only the selected entry and its import closure are bundled: 22
local modules, with 1 in Challenge's independent closure and
21 in Solution's. Archives, process notes, runtime sources and
build/dependency caches are excluded.

From `lean/`, using the pinned toolchain:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build Palomar.PaperOne.Challenge
LEAN_NUM_THREADS=1 lake build
LEAN_NUM_THREADS=1 lake comparator --config Palomar/PaperOne/comparator.json
```

The Comparator command uses its supported Linux sandbox. Local development
verification is recorded in metadata; it is separate from protected verification
of an immutable public snapshot. No registry submission is made by packaging.
The [manual preflight workflow](.github/workflows/palomar-preflight.yml) pins
pipeline `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.

Source checkpoint: `c397e7788ea43f378629d3c69445dfe3478eff0d`. The [manifest](PALOMAR_PACKAGE_MANIFEST.json) records source
hashes and navigation rewrites. Immutable upstream metadata URLs record
provenance; the bundled source is available for review. [MIT licence](LICENSE).
