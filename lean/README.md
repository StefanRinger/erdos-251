# Lean formalization

The package and namespace are **`PrimeGapNormality`**. The public entry
points are:

| Entry | Purpose |
| --- | --- |
| `PrimeGapNormality.Paper` | All mathematical results formalized for the paper |
| `PrimeGapNormality.PaperAudit` | Endpoint types and transitive axiom checks |

The default build includes **both** entries. `MainResults` is a smaller
headline collection; it is not a substitute for the complete paper target.
The internal `Core…` modules are individual proof components, not additional
user-facing build stages.

## Build

Install Lean through Elan, then run from this directory:

```sh
bash scripts/build-slot-run.sh lake exe cache get
bash scripts/build-slot-run.sh lake build
```

For a logged full build followed by freshness, source-integrity and
transitive-axiom checks, use `LEAN_NUM_THREADS=1 bash
scripts/build-paper-release.sh` instead of the second command. This script
already acquires a shared build slot; do not wrap it again. Its reports
are written to a new directory under `.local-verification/`.

`lean-toolchain` pins Lean 4.33.1. `lake-manifest.json` pins Mathlib and
its transitive dependencies to exact commits; do not run `lake update`
when reproducing this version. The cache command obtains upstream build
artifacts, not a substitute proof of this project's theorems.

The wrapper allows two simultaneous build commands by default and at most
three with `BUILD_SLOT_MAX=3`. Workers in different checkouts must set
`BUILD_SLOT_DIR` to the same absolute slot directory. Do not nest wrappers
or run a second independent build queue.

## What to check

1. Compare the actual theorem type with the paper, including its hypotheses.
2. Build `PaperAudit` and inspect the printed transitive axioms. Expected
   axioms are subsets of `propext`, `Classical.choice` and `Quot.sound`.
   Arithmetic conjectures must be explicit theorem premises, not new axioms.
3. Run the static source checks:

```sh
python3 scripts/core-source-manifest.py --entry PrimeGapNormality.Paper --entry PrimeGapNormality.PaperAudit
python3 scripts/core-trust-scan.py --entry PrimeGapNormality.Paper --entry PrimeGapNormality.PaperAudit
```

4. After building, optionally replay the complete imported environment:

```sh
bash scripts/kernel-replay.sh
```

The replay script already acquires a shared build slot. It checks freshness,
runs `leanchecker --fresh`, and compares source inventories before and after.
This uses Lean's kernel again, not an independently implemented kernel.
Neither the replay nor absence of `sorry` alone guarantees that a theorem
states the intended mathematical claim.

## Release verification status

The full `PrimeGapNormality` package has been built and audited successfully:
629 local modules and all 416 requested transitive axiom checks passed.
The compiled targets are `PrimeGapNormality.Paper` and
`PrimeGapNormality.PaperAudit`. Source and dependency inventories were
unchanged across the build, and the subsequent freshness check passed.
See [VERIFICATION.md](VERIFICATION.md) for the source-bound evidence and
the scope of the checks. No mathematical hypothesis or proof changed during
the public namespace relocation.

Only the required local import closure is included. Private research rounds,
build caches and abandoned proof paths are not release sources. Third-party
licenses and attribution are preserved in [THIRD_PARTY.md](THIRD_PARTY.md).

## License

The original code, scripts and repository documentation are licensed under
[Apache 2.0](../LICENSE). The accompanying paper is separately licensed
under [CC BY 4.0](../paper/LICENSE). Third-party licenses and notices remain
applicable; see [NOTICE](../NOTICE) and [THIRD_PARTY.md](THIRD_PARTY.md).
