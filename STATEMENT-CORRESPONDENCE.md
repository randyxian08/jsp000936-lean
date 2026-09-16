# JSP-000936 statement correspondence

Source: [Erdős problem 1129](https://www.erdosproblems.com/1129), the real
interval minimization question. The reviewed prize scope is the main
question, not the complex unit-circle variant mentioned in its discussion.

| Mathematical requirement | Lean representation |
| --- | --- |
| Exactly n distinct real nodes in [-1,1] | `Erdos1153.NodeFamily n` has `point : Fin n → ℝ`, injectivity and interval membership. |
| Literal Lagrange fundamental functions | `lagrangeFundamental` in `Erdos1153/Statement.lean` is the product of `(t-xᵢ)/(xₖ-xᵢ)` over `i ≠ k`. |
| Sum of absolute basis values | `lebesgueFunction` sums the absolute values over all original nodes. |
| Maximum over the full ambient interval | `amplification nodes := lebesgueOn nodes (-1) 1`. Continuity/compactness gives an attained maximum. |
| All placements compete, without prescribed endpoints | `IsMinimizer nodes := ∀ other : NodeFamily n, amplification nodes ≤ amplification other`. |
| Arbitrary enumeration | Consecutive nodes are identified using `nodes.sorted`; sorting preserves the Lebesgue function. |
| Every positive node count | `Target936` covers `NodeFamily 1`, then `NodeFamily (d+2)` for every natural d. |
| Existence of an optimum | `Target936` supplies a reference node family and proves `IsMinimizer reference`. |
| Characterization of all optima | `IsMinimizer nodes` iff `AdmissibleAffineCopy reference nodes` and both exterior endpoint values are at most `amplification reference`. |
| Fixed endpoints only for the reference | `IsNormalizedEquioscillating reference` pins the reference endpoints and equalizes its internal gap heights; competitors have no such restrictions. |
| Full-domain control, not just internal gaps | `full_interval_bound_of_gaps_and_endpoints` and exterior monotonicity in `FreeNodes.lean` control the entire ambient interval. |
| Executable target match | `Audit936.lean` checks `example : JSPFreeNodes.Target936 := JSPFreeNodes.jsp_000936` and prints its actual axiom dependencies. |

For a reference X*, admissible copies have sorted coordinates `c + s X*`,
with `s > 0` and `|c| + s ≤ 1`. The additional two endpoint inequalities
are essential. Equal internal peaks alone are not presented as sufficient
to minimize the ambient-interval Lebesgue constant.

This characterizes a possibly nonunique set of free-node minimizers.
Statements about a unique normalized configuration must not be silently
interpreted as uniqueness among all free-node configurations. Reviewers
should assess correspondence against the literal objective and original
mathematical sources, independently of informal uniqueness summaries.

The target definitions are unchanged from the supplied v2.1 candidate.
Compiler repairs changed proof terms only. JSP-000937's all-gap classification
is also included and checked, but its separate `Target937Logarithmic` remains
unproved; `Target937` is not a theorem in this submission.
