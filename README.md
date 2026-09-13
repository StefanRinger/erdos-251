# Local gap statistics, telescoping, and normality

Paper and Lean formalization by Stefan Ringer, motivated by
[Erdős problem 251](https://www.erdosproblems.com/251).

Under a uniform prime-tuples hypothesis, the paper proves normality of
geometrically weighted prime-gap series and classifies local polynomial
series by their weighted telescopes. It also treats joint distribution,
rational linear relations and quantitative digit statistics, as well as
unconditional results for rough numbers and a modified prime insertion clock.

The original prime-series problem remains open unconditionally. Different
bases generally define different numbers: absolute normality of one fixed
constant is not claimed. Precise assumptions and ranges are in the paper.

- **Paper:** [PDF](paper/prime_gap_normality.pdf) · [TeX source](paper/prime_gap_normality.tex)
- **Formalization:** [Lean sources and verification instructions](lean/README.md)

The public Lean package is `PrimeGapNormality`. Its complete paper and
audit entry points are `PrimeGapNormality.Paper` and
`PrimeGapNormality.PaperAudit`.

**Verification:** The complete `PrimeGapNormality` build and audit have
passed: 629 local modules and all 416 requested transitive axiom checks.
See [verification results](lean/VERIFICATION.md) for the source-bound evidence
and the scope of the checks.

## Reproduction and attribution

Lean and Mathlib versions are pinned; the Lean README explains the build,
axiom checks and optional full kernel replay. The paper records AI
assistance. Dependency authorship and licenses remain separate from the
authorship of this paper; see [third-party provenance](lean/THIRD_PARTY.md).

## License

- **Paper (TeX and PDF):** [Creative Commons Attribution 4.0 International
  (CC BY 4.0)](paper/LICENSE).
- **Original Lean code, scripts and repository documentation:**
  [Apache License 2.0](LICENSE).

Copyright 2026 Stefan Ringer. Third-party materials retain their existing
licenses and attribution; see [NOTICE](NOTICE) and
[third-party provenance](lean/THIRD_PARTY.md).
