# JSP-000936: free interpolation nodes on the real interval

Lean formalization submitted by [randyxian08](https://github.com/randyxian08).

The main result characterizes every minimizer of the Lebesgue constant
among all distinct real interpolation nodes in `[-1,1]`, without fixing
the extreme nodes. It also proves existence and treats the one-node case.

- Original problem: [Erdős 1129](https://www.erdosproblems.com/1129).
- Prize entry: [JSP-000936](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000936).
- Independent target: [`Target936`](Erdos1153/JSPInterpolation/Definitions.lean).
- Main theorem: [`JSPFreeNodes.jsp_000936`](Erdos1153/JSPInterpolation/FreeNodes.lean).
- [Statement correspondence](STATEMENT-CORRESPONDENCE.md).
- [Core provenance and authorship](PROVENANCE.md).

## Exact scope

The competitors are injective families of real nodes in `[-1,1]`, with arbitrary
enumeration. For one node every placement minimizes the Lebesgue constant.
For `n = d+2`, there exists a normalized equioscillating reference which
attains the global minimum. All minimizers are exactly its positive affine
copies lying in `[-1,1]` whose two exterior endpoint values do not exceed
the reference's optimal Lebesgue constant.

The fixed-endpoint condition applies to the reference only. There is no
claim that the unrestricted free-node minimizer is unique. The complex
unit-circle variant discussed in the bibliography is outside this submission.

The repository also contains the checked classification of maximizers for
JSP-000937's all-gap objective, including both exterior intervals. Its separate
uniform `O(log n)` bound has no Lean proof here. Accordingly, this repository
does not claim completion of the whole JSP-000937 problem. The JSP-000958
adapter reuses the pinned core theorem and is not a new nomination here.

## Reproduce

Install elan, Git and Python 3, then run:

```sh
bash verify.sh
```

Lean is pinned to 4.27.0 and Mathlib to v4.27.0, with the exact dependency
commits in `lake-manifest.json`. The verifier checks the declared scopes,
prints the actual axiom dependencies and rejects missing or unexpected
axiom reports and proof placeholders. Passing it does not assert the full
JSP-000937 target.

Local verification passed on macOS arm64 on 2026-09-16, reusing dependency
build artifacts. The repaired source modules were recompiled; the generated
single-file form was also checked in the local repair package. See
[evidence/local-verification.log](evidence/local-verification.log) for this
publication snapshot. Expected final axioms are `propext`, `Classical.choice`
and `Quot.sound`. GitHub Actions supplies an additional Linux reproduction;
consult its actual run status rather than assuming it has passed.

Kernel checking is separate from independent review of the formal statement,
authorship, priority, and award eligibility. This is a submission for review,
not an award announcement or a claim of payment approval.
