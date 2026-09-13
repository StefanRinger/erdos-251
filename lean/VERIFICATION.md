# Verification results

**Completed:** the full public `PrimeGapNormality` package has been built
and audited successfully, including both `Paper` and `PaperAudit`.
The build finished on 13 September 2026 at 21:21:35 UTC (23:21:35 CEST).
The source/artifact correspondence was rechecked on 14 September 2026.

## Completed checks

- **629 local modules:** genuine successful build traces and compiled
  artifacts, with no compiler errors.
- **416 requested transitive axiom checks:** all outputs present and
  matched to the requested theorem names. Their axiom union is exactly
  `propext`, `Classical.choice` and `Quot.sound`.
- **Full build and freshness:** exit code 0 for the two public targets;
  the subsequent no-build check reported `All targets up-to-date (4700 jobs)`.
  This job count includes dependency tasks, not 4700 independent theorems.
- **Source integrity:** source and dependency inventories were unchanged
  across the build. Current source, paper and artifact hashes match the
  saved acceptance evidence.
- **Static trust/import checks:** no missing local imports, import cycles,
  risky commands or unreviewed options reported.
- **Verification tooling:** 8 source-inventory, 6 trust-scan, 5 replay-wrapper,
  15 shared-limiter and 8 axiom-output parser tests passed. These are tests
  of the checking scripts, not mathematical proof certificates.

## Evidence and reproduction

- [Build/artifact bindings and all 416 axiom outputs](verification/completed/build-and-axioms.json)
- [Printed theorem types and axiom reports](verification/completed/theorem-types-and-axioms.txt)
- [Complete local source inventory](verification/core-source-manifest.json)
- [Static trust inventory](verification/core-trust-scan.json)
- [Paper SHA-256 binding](verification/paper-binding.json)

The [Lean README](README.md) gives the pinned build and audit commands.
Successful modules from earlier interrupted attempts were reused when
available; the completed full run checked the entire dependency graph.
Mathlib's existing dependency cache was used. This was not a clean build
on an independent machine, and no such reproduction is claimed.

## Scope and trust boundaries

The formalized theorem statements retain their explicit mathematical
hypotheses. In particular, the prime-tuples conjecture is not proved by
this build. Endpoint/statement review and the axiom audit are distinct:
kernel validity alone does not establish that a statement models the
intended mathematics.

An additional `leanchecker --fresh` replay of the pre-relocation proof
closure passed (exit 0, 2430.30 seconds), followed by successful source and
freshness checks. The 629 public sources correspond to that closure modulo
documented names and comments. That separate replay is not relabeled as a
replay of the renamed declarations. The renamed sources have their own
completed build and axiom audit documented above. The optional replay uses
Lean's own kernel, not an independently implemented kernel.
