# Classical prime number theorem: source provenance

This directory contains the required local port of
[PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
pinned at commit `a5154676af9aa3095150ee410cdda80555aa0642`.
Upstream citation metadata credits Alex Kontorovich and Terence Tao;
see [CITATION.upstream.cff](CITATION.upstream.cff). The upstream
[Apache-2.0 license](LICENSE) is retained byte-for-byte.

The upstream toolchain was Lean/Mathlib 4.32.2; the local port uses 4.33.1.
The source closure comprises the Wiener prefix through `WeakPNT`, Fourier,
Sobolev, smooth existence, support notation and asymptotics support. The
local `WeakPNT.lean` wrapper connects this result to the present project.

## Source transformations

1. Local imports are relocated under `PrimeGapNormality.ClassicalPNT`.
2. `Architect` imports, blueprint comments and blueprint metadata were
   removed, without removing their attached proofs.
3. An unused alternative Fourier-decay block was excluded: `prelim_decay_2`,
   its local `AbsolutelyContinuous` definition, `prelim_decay_3`, and
   `decay_alt`. Its placeholders were not replaced with assumptions.
   These declarations are not dependencies of the retained WeakPNT proof.
4. The unused bounded-variation import and the upstream declarations after
   the completed `WeakPNT` proof (upstream line 2461) were omitted.
5. Pre-import provenance headers use ordinary block comments, as required
   by the Lean 4.33 import parser.
6. Two unit-circle norm proofs use `Circle.norm_coe`; a measurable-product
   proof explicitly supplies continuity of `Multiplicative.ofAdd`; one
   null-singleton argument uses `mem_ae_iff` and `Measure.restrict_apply`.
   These are proof/API ports, not changes to mathematical statements.

Historical extraction-status comments inside sources describe that earlier
checkpoint, not acceptance of this release. The public tree is rebuilt
under its new module names; see [verification status](../../VERIFICATION.md).
There was no upstream `NOTICE` or `COPYING` file at the pinned commit.

The upstream authorship concerns the prime number theorem dependency,
not this paper's normality theorems. No project-wide license is inferred
from the license of this dependency.
