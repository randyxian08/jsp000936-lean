# Local Lean 4.33.0 verification — JSP-000936

Verified on 2026-09-23 in an isolated macOS build with Lean 4.33.0 and Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. The previous 4.27.0 log in this directory is historical evidence only.

- `lake build Erdos1153.JSPInterpolation.FreeNodes`: passed.
- `lake env lean Audit936.lean`: passed.
- `lake env leanchecker Erdos1153.JSPInterpolation.FreeNodes`: exited 0 with no diagnostics.
- `JSPFreeNodes.jsp_000936`: `#print axioms` returned `[propext, Classical.choice, Quot.sound]`.
- Source trust scan found no `sorry`, `admit`, `sorryAx`, `native_decide`, `implemented_by`, or new `axiom`, `unsafe`, or `opaque` declaration in the submitted proof sources.

These are submitter-run checks. Public Linux CI and independent statement, authorship, and priority review are separate.
