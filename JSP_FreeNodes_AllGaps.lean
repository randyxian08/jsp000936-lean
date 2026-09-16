import Erdos1153.GapPolynomial
import Erdos1153.DeBoorPinkus.Package
import Mathlib.Tactic.NormNum
import Erdos1153.ClassicalBound.EquioscillatingHeight
import Mathlib.Tactic
import Erdos1153.Interpolation

/-!
v2.2 compilation-repair package.

Generated from the source modules by tools/flatten.py.
See evidence/reproduction for compiler and axiom-audit results.
Includes Target936 and Target937Classification.
Does NOT supply a proof of Target937Logarithmic or the full Target937.

Upstream: Ethan Yang, ethn-y/erdos-1153-lean, MIT License.
Pinned commit: 03bd3e064c0b95e8e7d335fa0f3e3de0713ca777.
Toolchain: leanprover/lean4:v4.27.0; mathlib v4.27.0.
Build upstream first; check this file with lake env lean.
-/

/-! ===== Source module: Definitions.lean ===== -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Independent public statements for JSP-000936 and JSP-000937

This module imports interpolation definitions, NOT the de Boor--Pinkus
comparison theorem or any proof of either prize problem.

A competitor is the original `Erdos1153.NodeFamily`: an injective family of
points in [-1,1], with neither extreme node prescribed.  Sorting identifies
consecutive gaps without requiring the input enumeration to be increasing.
-/

namespace JSPFreeNodes
open Erdos1153
noncomputable section

/-! ## Literal objectives and an unrestricted competitor type -/

/-- The actual maximum of the Lebesgue function on the AMBIENT interval. -/
def amplification {n : ℕ} (nodes : NodeFamily n) : ℝ :=
  lebesgueOn nodes (-1) 1

/-- The actual minimum of the finitely many adjacent-gap maxima.
The type `Fin (d+1)` is nonempty, including the two-node case `d=0`. -/
def orderedMinPeak {d : ℕ} (nodes : OrderedNodes (d + 2)) : ℝ :=
  sInf (Set.range (fun i : Fin (d + 1) => gapHeight nodes i))

/-- For an arbitrarily enumerated node family, use its actual increasing
ordering to identify consecutive gaps. -/
def minPeak {d : ℕ} (nodes : NodeFamily (d + 2)) : ℝ :=
  orderedMinPeak nodes.sorted

/-- Global minimization over ALL distinct nodes in [-1,1]. -/
def IsMinimizer {n : ℕ} (nodes : NodeFamily n) : Prop :=
  ∀ other : NodeFamily n, amplification nodes ≤ amplification other

/-- Auxiliary INTERNAL-gap maximization over all node families.
This is NOT the original JSP-000937 objective. -/
def IsInternalMaximizer {d : ℕ} (nodes : NodeFamily (d + 2)) : Prop :=
  ∀ other : NodeFamily (d + 2), minPeak other ≤ minPeak nodes


/-- A normalized equioscillating REFERENCE configuration. This predicate is
required only of the existential reference, never of an arbitrary competitor. -/
def IsNormalizedEquioscillating {d : ℕ} (reference : NodeFamily (d + 2)) : Prop :=
  reference.sorted.point 0 = -1 ∧
  reference.sorted.point (Fin.last (d + 1)) = 1 ∧
  ∀ i j : Fin (d + 1),
    gapHeight reference.sorted i = gapHeight reference.sorted j

/-- A positive affine copy of the reference, with the affine map taking the
whole unit interval into itself. No endpoints of `nodes` are prescribed. -/
def AdmissibleAffineCopy {d : ℕ}
    (reference nodes : NodeFamily (d + 2)) : Prop :=
  ∃ c scale : ℝ, 0 < scale ∧ |c| + scale ≤ 1 ∧
    ∀ i, nodes.sorted.point i = c + scale * reference.sorted.point i

/-- Complete minimax statement for all positive cardinalities.

For one node every placement is optimal. For every n=d+2>=2 there is a
normalized equioscillating reference, attaining the global minimum over
ALL node families. Its admissible affine copies satisfying the two exterior
endpoint tests are EXACTLY all global minimizers. -/
def Target936 : Prop :=
  (∀ nodes : NodeFamily 1, IsMinimizer nodes) ∧
  ∀ d : ℕ, ∃ reference : NodeFamily (d + 2),
    IsNormalizedEquioscillating reference ∧
    IsMinimizer reference ∧
    ∀ nodes : NodeFamily (d + 2),
      amplification reference ≤ amplification nodes ∧
      (IsMinimizer nodes ↔
        AdmissibleAffineCopy reference nodes ∧
        lebesgueFunction nodes (-1) ≤ amplification reference ∧
        lebesgueFunction nodes 1 ≤ amplification reference)

/-- Auxiliary INTERNAL-gap maximin statement. Both exterior intervals
are omitted here; the original objective and target are stated below. -/
def TargetInternalMaximin : Prop :=
  ∀ d : ℕ, ∃ reference : NodeFamily (d + 2),
    IsNormalizedEquioscillating reference ∧
    IsInternalMaximizer reference ∧
    ∀ nodes : NodeFamily (d + 2),
      minPeak nodes ≤ minPeak reference ∧
      (IsInternalMaximizer nodes ↔ AdmissibleAffineCopy reference nodes)

/-! ## The original JSP-000937 objective INCLUDES the two exterior intervals -/

/-- The n+1 actual interval maxima, indexed without artificial interpolation
nodes. `none` is [-1,x_first], `some none` is [x_last,1], and
`some (some i)` is the i-th internal adjacent-node interval.
The added endpoints are interval boundaries, NOT additional interpolation
nodes; the Lagrange function still uses exactly d+2 original nodes. -/
def augmentedGapHeight {d : ℕ} (nodes : NodeFamily (d + 2)) :
    Option (Option (Fin (d + 1))) → ℝ
  | none => lebesgueOn nodes (-1) (nodes.sorted.point 0)
  | some none => lebesgueOn nodes (nodes.sorted.point (Fin.last (d + 1))) 1
  | some (some i) => gapHeight nodes.sorted i

/-- Literal minimum over ALL n+1 intervals, including both exterior intervals. -/
def allMinPeak {d : ℕ} (nodes : NodeFamily (d + 2)) : ℝ :=
  sInf (Set.range (augmentedGapHeight nodes))

/-- Original JSP-000937 maximization, over unrestricted node families. -/
def IsFullMaximizer {d : ℕ} (nodes : NodeFamily (d + 2)) : Prop :=
  ∀ other : NodeFamily (d + 2), allMinPeak other ≤ allMinPeak nodes

/-- The all-gap objective for one interpolation node has two exterior intervals. -/
def oneNodeAllMinPeak (nodes : NodeFamily 1) : ℝ :=
  min (lebesgueOn nodes (-1) (nodes.point 0))
    (lebesgueOn nodes (nodes.point 0) 1)

def IsOneNodeFullMaximizer (nodes : NodeFamily 1) : Prop :=
  ∀ other : NodeFamily 1, oneNodeAllMinPeak other ≤ oneNodeAllMinPeak nodes

/-- Exact free-node maximizer classification for the ORIGINAL all-gap objective.
The normalized reference describes the optimal SHAPE, but is not asserted
to maximize allMinPeak. A separately constructed compressed array attains
the value, and both exterior endpoint tests are necessary and sufficient. -/
def Target937Classification : Prop :=
  (∀ nodes : NodeFamily 1, IsOneNodeFullMaximizer nodes) ∧
  ∀ d : ℕ, ∃ reference : NodeFamily (d + 2),
    IsNormalizedEquioscillating reference ∧
    (∃ maximizer : NodeFamily (d + 2),
      IsFullMaximizer maximizer ∧
      allMinPeak maximizer = amplification reference) ∧
    ∀ nodes : NodeFamily (d + 2),
      allMinPeak nodes ≤ amplification reference ∧
      (IsFullMaximizer nodes ↔
        AdmissibleAffineCopy reference nodes ∧
        amplification reference ≤ lebesgueFunction nodes (-1) ∧
        amplification reference ≤ lebesgueFunction nodes 1)

/-- The other request in Erdős 1130: a uniform logarithmic upper bound.
This is deliberately separate from classification, so proving only the
classification cannot be mislabeled a proof of the entire original question. -/
def Target937Logarithmic : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ nodes : NodeFamily (d + 2),
    allMinPeak nodes ≤ C * Real.log ((d + 2 : ℕ) : ℝ)

/-- Full original JSP-000937 task, including BOTH requests. -/
def Target937 : Prop := Target937Classification ∧ Target937Logarithmic

end
end JSPFreeNodes


/-! ===== Source module: Canonical.lean ===== -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Canonical minimax and maximin consequences of de Boor--Pinkus

This file is only the fixed-endpoint lemma layer.  The public free-node
statements are in `Erdos1153.JSPInterpolation.FreeNodes`.

Upstream: Ethan Yang, ethn-y/erdos-1153-lean,
03bd3e064c0b95e8e7d335fa0f3e3de0713ca777 (MIT).

NEW CODE STATUS: not compiler-verified in the authoring environment.
-/

namespace JSPInterpolation

open Erdos1153 Erdos1153.DeBoorPinkus

noncomputable section

/-- No array other than the equioscillating array has all peaks at or below
its common height. This is the equality/uniqueness statement for minimax. -/
theorem upper_threshold_iff
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) :
    (∀ i, s.height i ≤ opt.height 0) ↔ s = opt := by
  constructor
  · intro h
    apply (comparisonPackage d A B).gapHeight_le_rigidity s opt
    intro i
    rw [hopt i 0]
    exact h i
  · intro h
    subst s
    intro i
    exact (hopt i 0).le

/-- No array other than the equioscillating array has all peaks at or above
its common height. This is the equality/uniqueness statement for maximin. -/
theorem lower_threshold_iff
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) :
    (∀ i, opt.height 0 ≤ s.height i) ↔ s = opt := by
  constructor
  · intro h
    have heq : opt = s := by
      apply (comparisonPackage d A B).gapHeight_le_rigidity opt s
      intro i
      rw [hopt i 0]
      exact h i
    exact heq.symm
  · intro h
    subst s
    intro i
    exact (hopt i 0).symm.le

/-- The optimal common peak is no larger than ANY upper bound for the
peaks of ANY competitor. In particular it is no larger than their maximum. -/
theorem optimal_le_any_peak_upper_bound
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) (U : ℝ)
    (hU : ∀ i, s.height i ≤ U) :
    opt.height 0 ≤ U := by
  classical
  by_contra h
  have hlt : U < opt.height 0 := lt_of_not_ge h
  have heq : s = opt :=
    (upper_threshold_iff opt hopt s).mp
      (fun i => (hU i).trans hlt.le)
  have hbad := hU 0
  rw [heq] at hbad
  exact (not_le_of_gt hlt) hbad

/-- ANY lower bound for all peaks of ANY competitor is no larger than the
optimal common peak. Apply this to the minimum of the competitor's peaks. -/
theorem any_peak_lower_bound_le_optimal
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) (L : ℝ)
    (hL : ∀ i, L ≤ s.height i) :
    L ≤ opt.height 0 := by
  classical
  by_contra h
  have hlt : opt.height 0 < L := lt_of_not_ge h
  have heq : s = opt :=
    (lower_threshold_iff opt hopt s).mp
      (fun i => hlt.le.trans (hL i))
  have hbad := hL 0
  rw [heq] at hbad
  exact (not_le_of_gt hlt) hbad

/-- A nonoptimal array has a peak strictly BELOW and a peak strictly ABOVE
the common optimal height. This proves the strict sandwich assertion. -/
theorem strict_peak_sandwich
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) (hne : s ≠ opt) :
    (∃ i, s.height i < opt.height 0) ∧
      (∃ j, opt.height 0 < s.height j) := by
  classical
  constructor
  · by_contra h
    have hbound : ∀ i, opt.height 0 ≤ s.height i := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    exact hne ((lower_threshold_iff opt hopt s).mp hbound)
  · by_contra h
    have hbound : ∀ i, s.height i ≤ opt.height 0 := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    exact hne ((upper_threshold_iff opt hopt s).mp hbound)

/-- Existence, minimax uniqueness, and maximin uniqueness for the canonical
arrays with extreme nodes -1 and 1. The number of nodes is d+2. -/
theorem jsp_000936_000937_canonical (d : ℕ) :
    ∃ opt : EndpointArray d (-1 : ℝ) 1,
      Equioscillates opt ∧
      ∀ s : EndpointArray d (-1 : ℝ) 1,
        ((∀ i, s.height i ≤ opt.height 0) ↔ s = opt) ∧
        ((∀ i, opt.height 0 ≤ s.height i) ↔ s = opt) := by
  have hAB : AdmissibleInterval (-1 : ℝ) 1 := by
    norm_num [AdmissibleInterval]
  obtain ⟨opt, hopt, _hunique⟩ :=
    existsUniqueEquioscillatingStatement d (-1 : ℝ) 1 hAB
  refine ⟨opt, hopt, ?_⟩
  intro s
  exact ⟨upper_threshold_iff opt hopt s,
    lower_threshold_iff opt hopt s⟩

end

end JSPInterpolation


/-! ===== Source module: FreeNodes.lean ===== -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JSP-000936 / JSP-000937: arbitrary, freely chosen interpolation nodes

Every public competitor below has type `NodeFamily (d + 2)`.  Its only
constraints are pairwise distinctness and membership in [-1,1].  There is
NO assumption that the extreme nodes equal -1 and 1, or that the original
enumeration is increasing.

The canonical endpoint array is a reference shape, not a restriction on
competitors.  Sorting, affine transport, both exterior intervals, the
actual maximum, and the actual minimum of the gap maxima are addressed.

The difficult de Boor--Pinkus theorem is imported from Ethan Yang's pinned
MIT-licensed project; it is not postulated as a new axiom here.

NEW CODE STATUS: complete proof-body candidate; NOT compiler-verified in
the authoring environment.  Run the supplied verify.sh before treating
these declarations as checked Lean theorems.
-/

namespace JSPFreeNodes

open Erdos1153 Erdos1153.DeBoorPinkus

noncomputable section

/-! ## Elementary maximum and finite-minimum interfaces -/

lemma value_le_interval_max {n : ℕ} (nodes : NodeFamily n)
    {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.Icc a b) :
    lebesgueFunction nodes x ≤ lebesgueOn nodes a b := by
  obtain ⟨t, _ht, heq, hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
  rw [heq]
  exact hmax x hx

lemma interval_max_le_iff {n : ℕ} (nodes : NodeFamily n)
    {a b U : ℝ} (hab : a ≤ b) :
    lebesgueOn nodes a b ≤ U ↔
      ∀ x ∈ Set.Icc a b, lebesgueFunction nodes x ≤ U := by
  constructor
  · intro h x hx
    exact (value_le_interval_max nodes hab hx).trans h
  · intro h
    obtain ⟨t, ht, heq, _hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
    rw [heq]
    exact h t ht

lemma orderedMinPeak_le {d : ℕ} (nodes : OrderedNodes (d + 2))
    (i : Fin (d + 1)) : orderedMinPeak nodes ≤ gapHeight nodes i := by
  classical
  exact csInf_le (Set.finite_range (fun j : Fin (d + 1) => gapHeight nodes j)).bddBelow
    (Set.mem_range_self i)

lemma le_orderedMinPeak_iff {d : ℕ} (nodes : OrderedNodes (d + 2)) (L : ℝ) :
    L ≤ orderedMinPeak nodes ↔ ∀ i : Fin (d + 1), L ≤ gapHeight nodes i := by
  constructor
  · intro h i
    exact h.trans (orderedMinPeak_le nodes i)
  · intro h
    apply le_csInf
    · exact ⟨gapHeight nodes (0 : Fin (d + 1)), ⟨0, rfl⟩⟩
    · rintro _ ⟨i, rfl⟩
      exact h i

lemma gap_le_amplification {d : ℕ} (nodes : OrderedNodes (d + 2))
    (i : Fin (d + 1)) : gapHeight nodes i ≤ amplification nodes.toNodeFamily := by
  change lebesgueOn nodes.toNodeFamily
      (nodes.point (gapLeftIndex i)) (nodes.point (gapRightIndex i)) ≤
    lebesgueOn nodes.toNodeFamily (-1) 1
  apply (interval_max_le_iff nodes.toNodeFamily (gap_left_lt_right nodes i).le).2
  intro x hx
  apply value_le_interval_max nodes.toNodeFamily (by norm_num)
  exact ⟨(nodes.neg_one_le _).trans hx.1, hx.2.trans (nodes.le_one _)⟩

/-! ## Sorting does not remove or constrain any node configurations -/

lemma ordered_ext {n : ℕ} {s t : OrderedNodes n}
    (h : ∀ i, s.point i = t.point i) : s = t := by
  have hbase : s.toNodeFamily = t.toNodeFamily := NodeFamily.ext (funext h)
  cases s
  cases t
  cases hbase
  rfl

lemma sorted_ordered_point {n : ℕ} (s : OrderedNodes n) (i : Fin n) :
    s.toNodeFamily.sorted.point i = s.point i := by
  have h := Finset.orderEmbOfFin_unique
    (NodeFamily.card_nodeFinset s.toNodeFamily)
    (fun k => (NodeFamily.mem_nodeFinset s.toNodeFamily _).2 ⟨k, rfl⟩)
    s.strictMono
  exact (congrFun h i).symm

@[simp]
lemma sorted_of_ordered {n : ℕ} (s : OrderedNodes n) :
    s.toNodeFamily.sorted = s :=
  ordered_ext (sorted_ordered_point s)

@[simp]
lemma sorted_endpoint_array {d : ℕ} {A B : ℝ} (s : EndpointArray d A B) :
    s.toNodeFamily.sorted = s.toOrderedNodes :=
  sorted_of_ordered s.toOrderedNodes

lemma amplification_sorted {n : ℕ} (nodes : NodeFamily n) :
    amplification nodes.sorted.toNodeFamily = amplification nodes :=
  NodeFamily.lebesgueOn_sorted nodes (-1) 1

/-! ## The actual extreme nodes, which are NOT assumed to be -1 and 1 -/

def left {d : ℕ} (nodes : OrderedNodes (d + 2)) : ℝ :=
  nodes.point (endpointLeftIndex d)

def right {d : ℕ} (nodes : OrderedNodes (d + 2)) : ℝ :=
  nodes.point (endpointRightIndex d)

/-- Regard a free ordered family as an endpoint array at its OWN endpoints. -/
def frame {d : ℕ} (nodes : OrderedNodes (d + 2)) :
    EndpointArray d (left nodes) (right nodes) where
  toOrderedNodes := nodes
  left_endpoint := rfl
  right_endpoint := rfl

lemma left_le_point {d : ℕ} (nodes : OrderedNodes (d + 2)) (i : Fin (d + 2)) :
    left nodes ≤ nodes.point i := by
  apply nodes.strictMono.monotone
  change (endpointLeftIndex d).val ≤ i.val
  simp

lemma point_le_right {d : ℕ} (nodes : OrderedNodes (d + 2)) (i : Fin (d + 2)) :
    nodes.point i ≤ right nodes := by
  apply nodes.strictMono.monotone
  change i.val ≤ (endpointRightIndex d).val
  simp only [endpointRightIndex_val]
  omega

/-! ## A genuine affine bijection, and transport of the literal products -/

/-- The increasing affine map taking -1 to A and 1 to B. -/
def affine (A B t : ℝ) : ℝ :=
  (A + B) / 2 + ((B - A) / 2) * t

/-- Its inverse when A < B. -/
def unaffine (A B x : ℝ) : ℝ :=
  (x - (A + B) / 2) / ((B - A) / 2)

@[simp]
lemma affine_neg_one (A B : ℝ) : affine A B (-1) = A := by
  unfold affine
  ring

@[simp]
lemma affine_one (A B : ℝ) : affine A B 1 = B := by
  unfold affine
  ring

lemma affine_strictMono {A B : ℝ} (hAB : A < B) : StrictMono (affine A B) := by
  have hs : (0 : ℝ) < (B - A) / 2 := by linarith
  intro u v huv
  change (A + B) / 2 + ((B - A) / 2) * u <
    (A + B) / 2 + ((B - A) / 2) * v
  exact add_lt_add_right (mul_lt_mul_of_pos_left huv hs) ((A + B) / 2)

lemma affine_unaffine {A B : ℝ} (hAB : A < B) (x : ℝ) :
    affine A B (unaffine A B x) = x := by
  have hs : (B - A) / 2 ≠ 0 := ne_of_gt (by linarith)
  have hcancel (c s : ℝ) (hs' : s ≠ 0) : c + s * ((x - c) / s) = x := by
    field_simp [hs']
    <;> ring
  exact hcancel _ _ hs

lemma unaffine_affine {A B : ℝ} (hAB : A < B) (t : ℝ) :
    unaffine A B (affine A B t) = t := by
  have hs : (B - A) / 2 ≠ 0 := ne_of_gt (by linarith)
  have hcancel (c s : ℝ) (hs' : s ≠ 0) : (c + s * t - c) / s = t := by
    field_simp [hs']
    <;> ring
  exact hcancel _ _ hs

lemma affine_mem_Icc {A B u v t : ℝ} (hAB : A < B)
    (ht : t ∈ Set.Icc u v) : affine A B t ∈ Set.Icc (affine A B u) (affine A B v) :=
  ⟨(affine_strictMono hAB).monotone ht.1, (affine_strictMono hAB).monotone ht.2⟩

lemma unaffine_mem_Icc {A B u v x : ℝ} (hAB : A < B)
    (hx : x ∈ Set.Icc (affine A B u) (affine A B v)) :
    unaffine A B x ∈ Set.Icc u v := by
  constructor
  · by_contra h
    have hlt := affine_strictMono hAB (lt_of_not_ge h)
    rw [affine_unaffine hAB x] at hlt
    exact (not_lt_of_ge hx.1) hlt
  · by_contra h
    have hlt := affine_strictMono hAB (lt_of_not_ge h)
    rw [affine_unaffine hAB x] at hlt
    exact (not_lt_of_ge hx.2) hlt

/-- An actual affine copy of the canonical array in ANY admissible [A,B]. -/
def affineNodes {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) : EndpointArray d A B where
  point i := affine A B (opt.point i)
  injective := (affine_strictMono hAB.2.1).injective.comp opt.injective
  mem_Icc i := by
    have hi := affine_mem_Icc hAB.2.1 (opt.mem_Icc i)
    rw [affine_neg_one, affine_one] at hi
    exact ⟨hAB.1.trans hi.1, hi.2.trans hAB.2.2⟩
  strictMono := (affine_strictMono hAB.2.1).comp opt.strictMono
  left_endpoint := by rw [opt.left_endpoint, affine_neg_one]
  right_endpoint := by rw [opt.right_endpoint, affine_one]

@[simp]
lemma affineNodes_point {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) (i : Fin (d + 2)) :
    (affineNodes opt hAB).point i = affine A B (opt.point i) := rfl

lemma lagrangeFundamental_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) (k : Fin (d + 2)) (t : ℝ) :
    lagrangeFundamental (affineNodes opt hAB).toNodeFamily k (affine A B t) =
      lagrangeFundamental opt.toNodeFamily k t := by
  classical
  unfold lagrangeFundamental
  apply Finset.prod_congr rfl
  intro j _hj
  have hs : (B - A) / 2 ≠ 0 := ne_of_gt (by linarith [hAB.2.1])
  change (affine A B t - affine A B (opt.point j)) /
      (affine A B (opt.point k) - affine A B (opt.point j)) =
    (t - opt.point j) / (opt.point k - opt.point j)
  have hdiff (u v : ℝ) : affine A B u - affine A B v = ((B - A) / 2) * (u - v) := by
    unfold affine
    ring
  rw [hdiff, hdiff]
  -- Cancel the common nonzero slope directly.  No field_simp normalization
  -- or polynomial reasoning about an inverse of B-A is needed.
  exact mul_div_mul_left _ _ hs

lemma lebesgueFunction_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) (t : ℝ) :
    lebesgueFunction (affineNodes opt hAB).toNodeFamily (affine A B t) =
      lebesgueFunction opt.toNodeFamily t := by
  classical
  unfold lebesgueFunction
  apply Finset.sum_congr rfl
  intro k _hk
  rw [lagrangeFundamental_affine]

/-- Invariance of interval maxima, proved by transporting both maximizers. -/
lemma lebesgueOn_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) {a b : ℝ} (hab : a ≤ b) :
    lebesgueOn (affineNodes opt hAB).toNodeFamily (affine A B a) (affine A B b) =
      lebesgueOn opt.toNodeFamily a b := by
  obtain ⟨u, hu, hu_eq, hu_max⟩ := exists_lebesgueOn_eq_and_ge
    (affineNodes opt hAB).toNodeFamily ((affine_strictMono hAB.2.1).monotone hab)
  obtain ⟨t, ht, ht_eq, ht_max⟩ := exists_lebesgueOn_eq_and_ge opt.toNodeFamily hab
  apply le_antisymm
  · rw [hu_eq, ht_eq]
    have hv := unaffine_mem_Icc hAB.2.1 hu
    rw [← affine_unaffine hAB.2.1 u, lebesgueFunction_affine]
    exact ht_max (unaffine A B u) hv
  · rw [hu_eq, ht_eq]
    have h := hu_max (affine A B t) (affine_mem_Icc hAB.2.1 ht)
    rw [lebesgueFunction_affine] at h
    exact h

lemma height_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    {A B : ℝ} (hAB : AdmissibleInterval A B) (i : Fin (d + 1)) :
    (affineNodes opt hAB).height i = opt.height i := by
  unfold EndpointArray.height gapHeight
  simpa only [affineNodes_point] using
    (lebesgueOn_affine opt hAB (gap_left_lt_right opt.toOrderedNodes i).le)

lemma equioscillates_affine {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) {A B : ℝ} (hAB : AdmissibleInterval A B) :
    Equioscillates (affineNodes opt hAB) := by
  intro i j
  rw [height_affine, height_affine]
  exact hopt i j

/-! ## Explicit affine shape, and its equivalent c + scale*x description -/

/-- Only the relative positions are fixed. The two extreme nodes are free. -/
def HasShape {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) : Prop :=
  ∀ i, nodes.sorted.point i =
    affine (left nodes.sorted) (right nodes.sorted) (opt.point i)

lemma frame_eq_affine_iff {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) :
    frame nodes.sorted = affineNodes opt (frame nodes.sorted).admissibleInterval ↔
      HasShape opt nodes := by
  constructor
  · intro h i
    exact congrArg (fun s : EndpointArray d (left nodes.sorted) (right nodes.sorted) =>
      s.point i) h
  · intro h
    apply EndpointArray.ext
    exact h

/-- The shape condition is literally a positive affine image fitting in [-1,1]. -/
lemma hasShape_iff_affine_copy {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) :
    HasShape opt nodes ↔
      ∃ c scale : ℝ, 0 < scale ∧ |c| + scale ≤ 1 ∧
        ∀ i, nodes.sorted.point i = c + scale * opt.point i := by
  constructor
  · intro h
    let a := left nodes.sorted
    let b := right nodes.sorted
    let c := (a + b) / 2
    let scale := (b - a) / 2
    have hab : a < b := (frame nodes.sorted).endpoints_lt
    have ha : -1 ≤ a := (frame nodes.sorted).neg_one_le_left
    have hb : b ≤ 1 := (frame nodes.sorted).right_le_one
    refine ⟨c, scale, ?_, ?_, ?_⟩
    · dsimp [scale]
      linarith
    · rcases le_total 0 c with hc | hc
      · rw [abs_of_nonneg hc]
        dsimp [c, scale]
        linarith
      · rw [abs_of_nonpos hc]
        dsimp [c, scale]
        linarith
    · exact h
  · rintro ⟨c, scale, _hscale, _hfit, hpoints⟩
    have ha := hpoints (endpointLeftIndex d)
    have hb := hpoints (endpointRightIndex d)
    rw [opt.left_endpoint] at ha
    rw [opt.right_endpoint] at hb
    change left nodes.sorted = c + scale * (-1) at ha
    change right nodes.sorted = c + scale * 1 at hb
    have hc : (left nodes.sorted + right nodes.sorted) / 2 = c := by linarith
    have hs : (right nodes.sorted - left nodes.sorted) / 2 = scale := by linarith
    intro i
    change nodes.sorted.point i =
      (left nodes.sorted + right nodes.sorted) / 2 +
        ((right nodes.sorted - left nodes.sorted) / 2) * opt.point i
    rw [hc, hs]
    exact hpoints i

/-! ## Bounds that already range over every free-node family -/

lemma canonical_amplification {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) :
    amplification opt.toNodeFamily = opt.height 0 :=
  ClassicalBound.lebesgueOn_eq_height_zero_of_equioscillates opt hopt

lemma ordered_amplification_lower_bound {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : OrderedNodes (d + 2)) :
    opt.height 0 ≤ amplification nodes.toNodeFamily := by
  have h := JSPInterpolation.optimal_le_any_peak_upper_bound
    (affineNodes opt (frame nodes).admissibleInterval)
    (equioscillates_affine opt hopt (frame nodes).admissibleInterval)
    (frame nodes) (amplification nodes.toNodeFamily)
    (fun i => gap_le_amplification nodes i)
  simpa only [height_affine] using h

lemma amplification_lower_bound {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : NodeFamily (d + 2)) :
    opt.height 0 ≤ amplification nodes := by
  have h := ordered_amplification_lower_bound opt hopt nodes.sorted
  rwa [amplification_sorted] at h

lemma minPeak_upper_bound {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : NodeFamily (d + 2)) :
    minPeak nodes ≤ opt.height 0 := by
  have h := JSPInterpolation.any_peak_lower_bound_le_optimal
    (affineNodes opt (frame nodes.sorted).admissibleInterval)
    (equioscillates_affine opt hopt (frame nodes.sorted).admissibleInterval)
    (frame nodes.sorted) (minPeak nodes)
    (fun i => orderedMinPeak_le nodes.sorted i)
  simpa only [height_affine] using h

lemma canonical_minPeak {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) : minPeak opt.toNodeFamily = opt.height 0 := by
  change orderedMinPeak opt.toOrderedNodes.toNodeFamily.sorted = opt.height 0
  rw [sorted_of_ordered]
  apply le_antisymm
  · exact orderedMinPeak_le opt.toOrderedNodes 0
  · apply (le_orderedMinPeak_iff opt.toOrderedNodes (opt.height 0)).2
    intro i
    exact (hopt i 0).symm.le

/-! ## Auxiliary internal-gap equality classification -/

lemma minPeak_eq_iff_shape {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : NodeFamily (d + 2)) :
    minPeak nodes = opt.height 0 ↔ HasShape opt nodes := by
  constructor
  · intro hmin
    apply (frame_eq_affine_iff opt nodes).1
    apply (JSPInterpolation.lower_threshold_iff
      (affineNodes opt (frame nodes.sorted).admissibleInterval)
      (equioscillates_affine opt hopt (frame nodes.sorted).admissibleInterval)
      (frame nodes.sorted)).1
    intro i
    rw [height_affine, ← hmin]
    exact orderedMinPeak_le nodes.sorted i
  · intro hshape
    have heq := (frame_eq_affine_iff opt nodes).2 hshape
    apply le_antisymm (minPeak_upper_bound opt hopt nodes)
    apply (le_orderedMinPeak_iff nodes.sorted (opt.height 0)).2
    intro i
    change opt.height 0 ≤ (frame nodes.sorted).height i
    rw [heq, height_affine]
    exact (hopt i 0).symm.le

lemma maximizer_iff_shape {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : NodeFamily (d + 2)) :
    IsInternalMaximizer nodes ↔ HasShape opt nodes := by
  rw [← minPeak_eq_iff_shape opt hopt nodes]
  constructor
  · intro h
    apply le_antisymm (minPeak_upper_bound opt hopt nodes)
    have h' := h opt.toNodeFamily
    rwa [canonical_minPeak opt hopt] at h'
  · intro h other
    rw [h]
    exact minPeak_upper_bound opt hopt other

/-! ## Exterior intervals: upper tests for 936, lower tests for 937 -/

/-- To the left of all nodes, moving farther left can only increase the
Lebesgue function.  This is proved factor by factor, not assumed. -/
lemma lebesgue_left_exterior {n : ℕ} (nodes : NodeFamily n) {u v : ℝ}
    (huv : u ≤ v) (hv : ∀ i, v ≤ nodes.point i) :
    lebesgueFunction nodes v ≤ lebesgueFunction nodes u := by
  classical
  unfold lebesgueFunction
  apply Finset.sum_le_sum
  intro k _hk
  simp only [lagrangeFundamental, Finset.abs_prod, abs_div]
  apply Finset.prod_le_prod
  · intro j _hj
    exact div_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro j _hj
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    rw [abs_of_nonpos (sub_nonpos.mpr (hv j)),
      abs_of_nonpos (sub_nonpos.mpr (huv.trans (hv j)))]
    linarith

/-- To the right of all nodes, moving farther right can only increase the
Lebesgue function. -/
lemma lebesgue_right_exterior {n : ℕ} (nodes : NodeFamily n) {u v : ℝ}
    (huv : u ≤ v) (hu : ∀ i, nodes.point i ≤ u) :
    lebesgueFunction nodes u ≤ lebesgueFunction nodes v := by
  classical
  unfold lebesgueFunction
  apply Finset.sum_le_sum
  intro k _hk
  simp only [lagrangeFundamental, Finset.abs_prod, abs_div]
  apply Finset.prod_le_prod
  · intro j _hj
    exact div_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro j _hj
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    rw [abs_of_nonneg (sub_nonneg.mpr (hu j)),
      abs_of_nonneg (sub_nonneg.mpr ((hu j).trans huv))]
    exact sub_le_sub_right huv _

/-- Pointwise control on the WHOLE ambient interval from all internal peaks
and the two ambient endpoint values. -/
lemma full_interval_bound_of_gaps_and_endpoints {d : ℕ}
    (nodes : OrderedNodes (d + 2)) (U : ℝ)
    (hgaps : ∀ i : Fin (d + 1), gapHeight nodes i ≤ U)
    (hleft : lebesgueFunction nodes.toNodeFamily (-1) ≤ U)
    (hright : lebesgueFunction nodes.toNodeFamily 1 ≤ U) :
    amplification nodes.toNodeFamily ≤ U := by
  apply (interval_max_le_iff nodes.toNodeFamily (by norm_num : (-1 : ℝ) ≤ 1)).2
  intro x hx
  rcases le_total x (left nodes) with hxl | hlx
  · exact (lebesgue_left_exterior nodes.toNodeFamily hx.1
      (fun i => hxl.trans (left_le_point nodes i))).trans hleft
  · rcases le_total (right nodes) x with hrx | hxr
    · exact (lebesgue_right_exterior nodes.toNodeFamily hx.2
        (fun i => (point_le_right nodes i).trans hrx)).trans hright
    · obtain ⟨i, hi⟩ := ClassicalBound.exists_closedGap_of_mem_Icc
        (frame nodes) ⟨hlx, hxr⟩
      exact (DeBoorPinkus.lebesgueFunction_le_height (frame nodes) i hi).trans (hgaps i)

/-! ## JSP-000936: exact equality classification over arbitrary node families -/

lemma amplification_eq_iff_shape_and_endpoints {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : NodeFamily (d + 2)) :
    amplification nodes = opt.height 0 ↔
      HasShape opt nodes ∧
      lebesgueFunction nodes (-1) ≤ opt.height 0 ∧
      lebesgueFunction nodes 1 ≤ opt.height 0 := by
  constructor
  · intro hmax
    refine ⟨?_, ?_, ?_⟩
    · apply (frame_eq_affine_iff opt nodes).1
      apply (JSPInterpolation.upper_threshold_iff
        (affineNodes opt (frame nodes.sorted).admissibleInterval)
        (equioscillates_affine opt hopt (frame nodes.sorted).admissibleInterval)
        (frame nodes.sorted)).1
      intro i
      rw [height_affine]
      calc
        (frame nodes.sorted).height i ≤ amplification nodes.sorted.toNodeFamily :=
          gap_le_amplification nodes.sorted i
        _ = amplification nodes := amplification_sorted nodes
        _ = opt.height 0 := hmax
    · exact (value_le_interval_max nodes (by norm_num)
        (by norm_num : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)).trans_eq hmax
    · exact (value_le_interval_max nodes (by norm_num)
        (by norm_num : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)).trans_eq hmax
  · rintro ⟨hshape, hleft, hright⟩
    have heq := (frame_eq_affine_iff opt nodes).2 hshape
    have hbound := full_interval_bound_of_gaps_and_endpoints nodes.sorted (opt.height 0)
      (fun i => by
        change (frame nodes.sorted).height i ≤ opt.height 0
        rw [heq, height_affine]
        exact (hopt i 0).le)
      (by rwa [NodeFamily.lebesgueFunction_sorted])
      (by rwa [NodeFamily.lebesgueFunction_sorted])
    rw [amplification_sorted] at hbound
    exact le_antisymm hbound (amplification_lower_bound opt hopt nodes)

lemma minimizer_iff_shape_and_endpoints {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : NodeFamily (d + 2)) :
    IsMinimizer nodes ↔
      HasShape opt nodes ∧
      lebesgueFunction nodes (-1) ≤ opt.height 0 ∧
      lebesgueFunction nodes 1 ≤ opt.height 0 := by
  rw [← amplification_eq_iff_shape_and_endpoints opt hopt nodes]
  constructor
  · intro h
    apply le_antisymm _ (amplification_lower_bound opt hopt nodes)
    exact (h opt.toNodeFamily).trans_eq (canonical_amplification opt hopt)
  · intro h other
    rw [h]
    exact amplification_lower_bound opt hopt other

/-! ## A normalized-coordinate version of the two exterior tests -/

lemma lebesgueFunction_of_shape {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) (hshape : HasShape opt nodes) (t : ℝ) :
    lebesgueFunction nodes (affine (left nodes.sorted) (right nodes.sorted) t) =
      lebesgueFunction opt.toNodeFamily t := by
  have heq := (frame_eq_affine_iff opt nodes).2 hshape
  have hbase := congrArg
    (fun s : EndpointArray d (left nodes.sorted) (right nodes.sorted) => s.toNodeFamily) heq
  dsimp only at hbase
  rw [← NodeFamily.lebesgueFunction_sorted nodes]
  change lebesgueFunction (frame nodes.sorted).toNodeFamily
      (affine (left nodes.sorted) (right nodes.sorted) t) = _
  rw [hbase]
  exact lebesgueFunction_affine opt (frame nodes.sorted).admissibleInterval t


lemma lebesgueFunction_of_shape_inverse {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) (hshape : HasShape opt nodes) (x : ℝ) :
    lebesgueFunction nodes x = lebesgueFunction opt.toNodeFamily
      (unaffine (left nodes.sorted) (right nodes.sorted) x) := by
  have h := lebesgueFunction_of_shape opt nodes hshape
    (unaffine (left nodes.sorted) (right nodes.sorted) x)
  rwa [affine_unaffine (frame nodes.sorted).endpoints_lt] at h

lemma minimizer_iff_normalized_exterior_tests {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : NodeFamily (d + 2)) :
    IsMinimizer nodes ↔ HasShape opt nodes ∧
      lebesgueFunction opt.toNodeFamily
        (unaffine (left nodes.sorted) (right nodes.sorted) (-1)) ≤ opt.height 0 ∧
      lebesgueFunction opt.toNodeFamily
        (unaffine (left nodes.sorted) (right nodes.sorted) 1) ≤ opt.height 0 := by
  rw [minimizer_iff_shape_and_endpoints opt hopt nodes]
  constructor
  · rintro ⟨hs, hl, hr⟩
    exact ⟨hs, (lebesgueFunction_of_shape_inverse opt nodes hs (-1)) ▸ hl,
      (lebesgueFunction_of_shape_inverse opt nodes hs 1) ▸ hr⟩
  · rintro ⟨hs, hl, hr⟩
    exact ⟨hs, (lebesgueFunction_of_shape_inverse opt nodes hs (-1)).symm ▸ hl,
      (lebesgueFunction_of_shape_inverse opt nodes hs 1).symm ▸ hr⟩

/-! ## Public, assumption-free conclusions for the two prize problems -/

/-- JSP-000936, full free-node version: existence, optimal value, and ALL
minimizers.  The only fixed-endpoint array is the reference shape. -/
theorem jsp_000936_free (d : ℕ) :
    ∃ opt : EndpointArray d (-1) 1,
      Equioscillates opt ∧
      IsMinimizer opt.toNodeFamily ∧
      amplification opt.toNodeFamily = opt.height 0 ∧
      ∀ nodes : NodeFamily (d + 2),
        opt.height 0 ≤ amplification nodes ∧
        (IsMinimizer nodes ↔
          HasShape opt nodes ∧
          lebesgueFunction nodes (-1) ≤ opt.height 0 ∧
          lebesgueFunction nodes 1 ≤ opt.height 0) := by
  obtain ⟨opt, hopt, _hunique⟩ :=
    existsUniqueEquioscillatingStatement d (-1) 1 (by norm_num [AdmissibleInterval])
  refine ⟨opt, hopt, ?_, canonical_amplification opt hopt, ?_⟩
  · intro other
    rw [canonical_amplification opt hopt]
    exact amplification_lower_bound opt hopt other
  · intro nodes
    exact ⟨amplification_lower_bound opt hopt nodes,
      minimizer_iff_shape_and_endpoints opt hopt nodes⟩

/-- Auxiliary INTERNAL-gap maximin theorem. This is not the full
JSP-000937 objective, which also includes the two exterior intervals. -/
theorem internal_maximin_free (d : ℕ) :
    ∃ opt : EndpointArray d (-1) 1,
      Equioscillates opt ∧
      IsInternalMaximizer opt.toNodeFamily ∧
      minPeak opt.toNodeFamily = opt.height 0 ∧
      ∀ nodes : NodeFamily (d + 2),
        minPeak nodes ≤ opt.height 0 ∧
        (IsInternalMaximizer nodes ↔
          ∃ c scale : ℝ, 0 < scale ∧ |c| + scale ≤ 1 ∧
            ∀ i, nodes.sorted.point i = c + scale * opt.point i) := by
  obtain ⟨opt, hopt, _hunique⟩ :=
    existsUniqueEquioscillatingStatement d (-1) 1 (by norm_num [AdmissibleInterval])
  refine ⟨opt, hopt, ?_, canonical_minPeak opt hopt, ?_⟩
  · intro other
    rw [canonical_minPeak opt hopt]
    exact minPeak_upper_bound opt hopt other
  · intro nodes
    exact ⟨minPeak_upper_bound opt hopt nodes,
      (maximizer_iff_shape opt hopt nodes).trans (hasShape_iff_affine_copy opt nodes)⟩

/-- The n=1 edge case of minimax: every single node has amplification one.
There are no INTERNAL adjacent gaps for n=1; the all-gap extension has
two exterior intervals, each with constant Lebesgue function one. -/
lemma single_node_lebesgue (nodes : NodeFamily 1) (x : ℝ) :
    lebesgueFunction nodes x = 1 := by
  classical
  have hfund (k : Fin 1) : lagrangeFundamental nodes k x = 1 := by
    have herase : (Finset.univ : Finset (Fin 1)).erase k = ∅ := by
      apply Finset.ext
      intro j
      have hjk : j = k := Subsingleton.elim j k
      simp [hjk]
    simp only [lagrangeFundamental, herase, Finset.prod_empty]
  simp [lebesgueFunction, hfund]

lemma single_node_amplification (nodes : NodeFamily 1) :
    amplification nodes = 1 := by
  obtain ⟨x, _hx, heq, _hmax⟩ := exists_lebesgueOn_eq_and_ge nodes
    (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num)
  exact heq.trans (single_node_lebesgue nodes x)

theorem jsp_000936_one_node (nodes : NodeFamily 1) : IsMinimizer nodes := by
  intro other
  calc
    amplification nodes = 1 := single_node_amplification nodes
    _ ≤ 1 := le_rfl
    _ = amplification other := (single_node_amplification other).symm


/-! ## Closed public targets whose competitor types contain no fixed endpoints -/

lemma canonical_is_normalized {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) : IsNormalizedEquioscillating opt.toNodeFamily := by
  unfold IsNormalizedEquioscillating
  simp only [sorted_endpoint_array]
  exact ⟨opt.left_endpoint, opt.right_endpoint, hopt⟩

lemma hasShape_iff_admissibleAffineCopy {d : ℕ} (opt : EndpointArray d (-1) 1)
    (nodes : NodeFamily (d + 2)) :
    HasShape opt nodes ↔ AdmissibleAffineCopy opt.toNodeFamily nodes := by
  simpa only [AdmissibleAffineCopy, sorted_of_ordered] using
    (hasShape_iff_affine_copy opt nodes)

/-- JSP-000936 in the independently stated, unrestricted-node interface. -/
theorem jsp_000936 : Target936 := by
  constructor
  · exact jsp_000936_one_node
  · intro d
    obtain ⟨opt, hopt, _hunique⟩ :=
      existsUniqueEquioscillatingStatement d (-1) 1 (by norm_num [AdmissibleInterval])
    refine ⟨opt.toNodeFamily, canonical_is_normalized opt hopt, ?_, ?_⟩
    · intro other
      rw [canonical_amplification opt hopt]
      exact amplification_lower_bound opt hopt other
    · intro nodes
      constructor
      · rw [canonical_amplification opt hopt]
        exact amplification_lower_bound opt hopt nodes
      · rw [canonical_amplification opt hopt,
          ← hasShape_iff_admissibleAffineCopy opt nodes]
        exact minimizer_iff_shape_and_endpoints opt hopt nodes

/-- Auxiliary internal-gap problem. See AllGaps.lean for the original
JSP-000937 objective, with both exterior intervals included. -/
theorem internal_maximin : TargetInternalMaximin := by
  intro d
  obtain ⟨opt, hopt, _hunique⟩ :=
    existsUniqueEquioscillatingStatement d (-1) 1 (by norm_num [AdmissibleInterval])
  refine ⟨opt.toNodeFamily, canonical_is_normalized opt hopt, ?_, ?_⟩
  · intro other
    rw [canonical_minPeak opt hopt]
    exact minPeak_upper_bound opt hopt other
  · intro nodes
    constructor
    · rw [canonical_minPeak opt hopt]
      exact minPeak_upper_bound opt hopt nodes
    · exact (maximizer_iff_shape opt hopt nodes).trans
        (hasShape_iff_admissibleAffineCopy opt nodes)

end
end JSPFreeNodes


/-! ===== Source module: AllGaps.lean ===== -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JSP-000937: the ORIGINAL all-gap maximin problem

Unlike the auxiliary internal-gap maximin problem, Erdős 1130 includes
[-1,x_first] and [x_last,1].  The proof below includes both intervals,
proves attainment by an explicitly compressed pattern, and classifies
all maximizers.  The independent logarithmic-growth request is separately
named in Definitions.lean; this file does not silently assume that request.

STATUS: newly written proof-body candidate, NOT compiler-verified here.
-/

namespace JSPFreeNodes
open Erdos1153 Erdos1153.DeBoorPinkus
noncomputable section

lemma allMinPeak_le {d : ℕ} (nodes : NodeFamily (d + 2))
    (i : Option (Option (Fin (d + 1)))) :
    allMinPeak nodes ≤ augmentedGapHeight nodes i := by
  classical
  exact csInf_le (Set.finite_range (augmentedGapHeight nodes)).bddBelow
    (Set.mem_range_self i)

lemma le_allMinPeak_iff {d : ℕ} (nodes : NodeFamily (d + 2)) (L : ℝ) :
    L ≤ allMinPeak nodes ↔ ∀ i, L ≤ augmentedGapHeight nodes i := by
  constructor
  · intro h i
    exact h.trans (allMinPeak_le nodes i)
  · intro h
    apply le_csInf
    · exact ⟨augmentedGapHeight nodes none, ⟨none, rfl⟩⟩
    · rintro _ ⟨i, rfl⟩
      exact h i

/-- Neither endpoint is inserted into the interpolating node family. The
maximum on each exterior interval is attained at the ambient endpoint. -/
lemma left_exterior_max {d : ℕ} (nodes : NodeFamily (d + 2)) :
    lebesgueOn nodes (-1) (nodes.sorted.point 0) =
      lebesgueFunction nodes (-1) := by
  have hab : (-1 : ℝ) ≤ nodes.sorted.point 0 := nodes.sorted.neg_one_le 0
  apply le_antisymm
  · apply (interval_max_le_iff nodes hab).2
    intro x hx
    have hxj (j : Fin (d + 2)) : x ≤ nodes.point j := by
      obtain ⟨i, hi⟩ := nodes.sortingPerm.surjective j
      rw [← hi, NodeFamily.point_sortingPerm]
      exact hx.2.trans (nodes.sorted.strictMono.monotone (Fin.zero_le i))
    exact lebesgue_left_exterior nodes hx.1 hxj
  · exact value_le_interval_max nodes hab ⟨le_rfl, hab⟩

lemma right_exterior_max {d : ℕ} (nodes : NodeFamily (d + 2)) :
    lebesgueOn nodes (nodes.sorted.point (Fin.last (d + 1))) 1 =
      lebesgueFunction nodes 1 := by
  have hab : nodes.sorted.point (Fin.last (d + 1)) ≤ (1 : ℝ) :=
    nodes.sorted.le_one _
  apply le_antisymm
  · apply (interval_max_le_iff nodes hab).2
    intro x hx
    have hjx (j : Fin (d + 2)) : nodes.point j ≤ x := by
      obtain ⟨i, hi⟩ := nodes.sortingPerm.surjective j
      rw [← hi, NodeFamily.point_sortingPerm]
      exact (nodes.sorted.strictMono.monotone (Fin.le_last i)).trans hx.1
    exact lebesgue_right_exterior nodes hx.2 hjx
  · exact value_le_interval_max nodes hab ⟨hab, le_rfl⟩

lemma allMinPeak_le_internal {d : ℕ} (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes ≤ minPeak nodes := by
  apply (le_orderedMinPeak_iff nodes.sorted _).2
  intro i
  exact allMinPeak_le nodes (some (some i))

/-- The literal minimum over n+1 intervals is exactly the three-way minimum
of the left exterior peak, the internal-gap minimum, and the right exterior peak. -/
lemma allMinPeak_eq_min {d : ℕ} (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes = min (lebesgueFunction nodes (-1))
      (min (minPeak nodes) (lebesgueFunction nodes 1)) := by
  apply le_antisymm
  · apply le_min
    · simpa only [augmentedGapHeight, left_exterior_max] using allMinPeak_le nodes none
    · apply le_min
      · exact allMinPeak_le_internal nodes
      · simpa only [augmentedGapHeight, right_exterior_max] using
          allMinPeak_le nodes (some none)
  · apply (le_allMinPeak_iff nodes _).2
    intro i
    cases i with
    | none =>
      simpa only [augmentedGapHeight, left_exterior_max] using
        (min_le_left (lebesgueFunction nodes (-1))
          (min (minPeak nodes) (lebesgueFunction nodes 1)))
    | some j =>
      cases j with
      | none =>
        change min (lebesgueFunction nodes (-1))
          (min (minPeak nodes) (lebesgueFunction nodes 1)) ≤
          lebesgueOn nodes (nodes.sorted.point (Fin.last (d + 1))) 1
        rw [right_exterior_max]
        exact (min_le_right _ _).trans (min_le_right _ _)
      | some g =>
        exact (min_le_right _ _).trans
          ((min_le_left _ _).trans (orderedMinPeak_le nodes.sorted g))

lemma allMinPeak_upper_bound {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes ≤ opt.height 0 :=
  (allMinPeak_le_internal nodes).trans (minPeak_upper_bound opt hopt nodes)

lemma allMinPeak_eq_iff_shape_and_endpoints {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes = opt.height 0 ↔
      HasShape opt nodes ∧
      opt.height 0 ≤ lebesgueFunction nodes (-1) ∧
      opt.height 0 ≤ lebesgueFunction nodes 1 := by
  constructor
  · intro heq
    have hle : opt.height 0 ≤ allMinPeak nodes := heq.ge
    have hleft := (le_allMinPeak_iff nodes _).1 hle none
    have hright := (le_allMinPeak_iff nodes _).1 hle (some none)
    have hint : minPeak nodes = opt.height 0 :=
      le_antisymm (minPeak_upper_bound opt hopt nodes)
        (hle.trans (allMinPeak_le_internal nodes))
    refine ⟨(minPeak_eq_iff_shape opt hopt nodes).1 hint, ?_, ?_⟩
    · simpa only [augmentedGapHeight, left_exterior_max] using hleft
    · simpa only [augmentedGapHeight, right_exterior_max] using hright
  · rintro ⟨hshape, hleft, hright⟩
    apply le_antisymm (allMinPeak_upper_bound opt hopt nodes)
    rw [allMinPeak_eq_min]
    apply le_min hleft
    apply le_min
    · exact ((minPeak_eq_iff_shape opt hopt nodes).2 hshape).ge
    · exact hright

/-! ## Actual attainment, not an unproved assumption about exterior growth -/

/-- Exactness of interpolation for p(X)=X bounds the exterior Lebesgue
function below whenever every node lies in [-a,a]. -/
lemma abs_le_scale_mul_lebesgue {d : ℕ} (nodes : NodeFamily (d + 2))
    (a x : ℝ) (ha : ∀ k, |nodes.point k| ≤ a) :
    |x| ≤ a * lebesgueFunction nodes x := by
  have hp : (Polynomial.X : Polynomial ℝ).degree < (d + 2 : ℕ) := by
    rw [Polynomial.degree_X]
    exact_mod_cast (show (1 : ℕ) < d + 2 by omega)
  simpa only [Polynomial.eval_X] using
    (abs_eval_le_mul_lebesgueFunction nodes Polynomial.X hp a x
      (by simpa only [Polynomial.eval_X] using ha))

/-- An explicit compression of the equioscillating pattern attains the
all-gap optimum.  No divergent-limit theorem or selection assumption is used. -/
lemma exists_allMinPeak_eq {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) :
    ∃ nodes : NodeFamily (d + 2), allMinPeak nodes = opt.height 0 := by
  let R : ℝ := |opt.height 0| + 2
  let a : ℝ := 1 / R
  have hR : 1 < R := by dsimp [R]; linarith [abs_nonneg (opt.height 0)]
  have hRpos : 0 < R := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    exact (div_le_iff₀ hRpos).2 (by linarith)
  have hAR : a * R = 1 := by
    dsimp [a]
    field_simp [ne_of_gt hRpos]
  have hab : AdmissibleInterval (-a) a := by
    exact ⟨by linarith, by linarith, ha1⟩
  let compressed : EndpointArray d (-a) a := affineNodes opt hab
  have hpoint (k : Fin (d + 2)) : compressed.point k = a * opt.point k := by
    change affine (-a) a (opt.point k) = _
    unfold affine
    ring
  have hsmall (k : Fin (d + 2)) : |compressed.point k| ≤ a := by
    rw [hpoint, abs_mul, abs_of_pos ha]
    have hk : |opt.point k| ≤ 1 := abs_le.mpr (opt.mem_Icc k)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hk ha.le
  have hshape : HasShape opt compressed.toNodeFamily := by
    unfold HasShape
    rw [sorted_endpoint_array]
    intro k
    have hl : left compressed.toOrderedNodes = -a := compressed.left_endpoint
    have hr : right compressed.toOrderedNodes = a := compressed.right_endpoint
    rw [hl, hr]
    rfl
  have hendpoint (x : ℝ) (hx : |x| = 1) :
      opt.height 0 ≤ lebesgueFunction compressed.toNodeFamily x := by
    have hxbound := abs_le_scale_mul_lebesgue compressed.toNodeFamily a x hsmall
    rw [hx] at hxbound
    have hRR : R ≤ lebesgueFunction compressed.toNodeFamily x := by
      by_contra h
      have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge h) ha
      rw [hAR] at hlt
      linarith
    exact (by dsimp [R]; linarith [le_abs_self (opt.height 0)] : opt.height 0 ≤ R).trans hRR
  refine ⟨compressed.toNodeFamily,
    (allMinPeak_eq_iff_shape_and_endpoints opt hopt compressed.toNodeFamily).2 ?_⟩
  exact ⟨hshape, hendpoint (-1) (by norm_num), hendpoint 1 (by norm_num)⟩

lemma full_maximizer_iff_eq {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (nodes : NodeFamily (d + 2)) :
    IsFullMaximizer nodes ↔ allMinPeak nodes = opt.height 0 := by
  constructor
  · intro hmax
    obtain ⟨witness, hwitness⟩ := exists_allMinPeak_eq opt hopt
    apply le_antisymm (allMinPeak_upper_bound opt hopt nodes)
    rw [← hwitness]
    exact hmax witness
  · intro heq other
    rw [heq]
    exact allMinPeak_upper_bound opt hopt other

lemma full_maximizer_iff_shape_and_endpoints {d : ℕ}
    (opt : EndpointArray d (-1) 1) (hopt : Equioscillates opt)
    (nodes : NodeFamily (d + 2)) :
    IsFullMaximizer nodes ↔
      HasShape opt nodes ∧
      opt.height 0 ≤ lebesgueFunction nodes (-1) ∧
      opt.height 0 ≤ lebesgueFunction nodes 1 :=
  (full_maximizer_iff_eq opt hopt nodes).trans
    (allMinPeak_eq_iff_shape_and_endpoints opt hopt nodes)

lemma oneNodeAllMinPeak_eq_one (nodes : NodeFamily 1) :
    oneNodeAllMinPeak nodes = 1 := by
  have hmax {a b : ℝ} (hab : a ≤ b) : lebesgueOn nodes a b = 1 := by
    obtain ⟨t, _ht, heq, _hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
    exact heq.trans (single_node_lebesgue nodes t)
  unfold oneNodeAllMinPeak
  rw [hmax (nodes.mem_Icc 0).1, hmax (nodes.mem_Icc 0).2, min_self]

theorem jsp_000937_one_node (nodes : NodeFamily 1) : IsOneNodeFullMaximizer nodes := by
  intro other
  calc
    oneNodeAllMinPeak other = 1 := oneNodeAllMinPeak_eq_one other
    _ ≤ 1 := le_rfl
    _ = oneNodeAllMinPeak nodes := (oneNodeAllMinPeak_eq_one nodes).symm

/-- Complete classification for the actual all-gap maximization. This theorem
has no fixed-endpoint hypotheses on any competitor. -/
theorem jsp_000937_classification : Target937Classification := by
  constructor
  · exact jsp_000937_one_node
  · intro d
    obtain ⟨opt, hopt, _hunique⟩ :=
      existsUniqueEquioscillatingStatement d (-1) 1 (by norm_num [AdmissibleInterval])
    refine ⟨opt.toNodeFamily, canonical_is_normalized opt hopt, ?_, ?_⟩
    · obtain ⟨witness, hwitness⟩ := exists_allMinPeak_eq opt hopt
      refine ⟨witness, (full_maximizer_iff_eq opt hopt witness).2 hwitness, ?_⟩
      rw [canonical_amplification opt hopt]
      exact hwitness
    · intro nodes
      rw [canonical_amplification opt hopt]
      constructor
      · exact allMinPeak_upper_bound opt hopt nodes
      · rw [← hasShape_iff_admissibleAffineCopy opt nodes]
        exact full_maximizer_iff_shape_and_endpoints opt hopt nodes

/-- A useful unconditional transfer theorem: the minimum peak of ANY node
array is no greater than the global Lebesgue constant of ANY competing
node array of the same cardinality. -/
theorem allMinPeak_le_any_amplification {d : ℕ}
    (nodes competitor : NodeFamily (d + 2)) :
    allMinPeak nodes ≤ amplification competitor := by
  obtain ⟨opt, hopt, _hunique⟩ :=
    existsUniqueEquioscillatingStatement d (-1) 1 (by norm_num [AdmissibleInterval])
  exact (allMinPeak_upper_bound opt hopt nodes).trans
    (amplification_lower_bound opt hopt competitor)

end
end JSPFreeNodes


/-! ===== Source module: Regression.lean ===== -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Semantic regression checks: fixing the extreme interpolation nodes to
-1 and 1 makes the ORIGINAL all-gap objective identically one.  This is
precisely why the fixed-endpoint internal-gap result must not be substituted
for JSP-000937. New proof-body candidates; not compiler-verified here. -/

namespace JSPFreeNodes
open Erdos1153 Erdos1153.DeBoorPinkus
noncomputable section

lemma one_le_internal_minPeak {d : ℕ} (nodes : NodeFamily (d + 2)) :
    1 ≤ minPeak nodes := by
  apply (le_orderedMinPeak_iff nodes.sorted 1).2
  intro i
  change 1 ≤ lebesgueOn nodes.sorted.toNodeFamily
    (nodes.sorted.point (gapLeftIndex i)) (nodes.sorted.point (gapRightIndex i))
  have hval := value_le_interval_max nodes.sorted.toNodeFamily
    (gap_left_lt_right nodes.sorted i).le
    (show nodes.sorted.point (gapLeftIndex i) ∈
      Set.Icc (nodes.sorted.point (gapLeftIndex i))
        (nodes.sorted.point (gapRightIndex i)) from
      ⟨le_rfl, (gap_left_lt_right nodes.sorted i).le⟩)
  simpa only [lebesgueFunction_at_node] using hval

/-- The all-gap minimum of EVERY endpoint-fixed node array is exactly one,
regardless of whether its internal peaks equioscillate. -/
theorem canonical_allMinPeak_eq_one {d : ℕ} (opt : EndpointArray d (-1) 1) :
    allMinPeak opt.toNodeFamily = 1 := by
  have hl : lebesgueFunction opt.toNodeFamily (-1) = 1 := by
    calc
      lebesgueFunction opt.toNodeFamily (-1) =
          lebesgueFunction opt.toNodeFamily (opt.point (endpointLeftIndex d)) :=
        congrArg (lebesgueFunction opt.toNodeFamily) opt.left_endpoint.symm
      _ = 1 := lebesgueFunction_at_node opt.toNodeFamily (endpointLeftIndex d)
  have hr : lebesgueFunction opt.toNodeFamily 1 = 1 := by
    calc
      lebesgueFunction opt.toNodeFamily 1 =
          lebesgueFunction opt.toNodeFamily (opt.point (endpointRightIndex d)) :=
        congrArg (lebesgueFunction opt.toNodeFamily) opt.right_endpoint.symm
      _ = 1 := lebesgueFunction_at_node opt.toNodeFamily (endpointRightIndex d)
  rw [allMinPeak_eq_min, hl, hr]
  rw [min_eq_right (one_le_internal_minPeak opt.toNodeFamily), min_self]

/-- Whenever the canonical internal height exceeds one, fixing the
extreme nodes gives a configuration that does NOT maximize the original
all-gap objective. -/
theorem canonical_not_full_maximizer {d : ℕ} (opt : EndpointArray d (-1) 1)
    (hopt : Equioscillates opt) (hheight : 1 < opt.height 0) :
    ¬ IsFullMaximizer opt.toNodeFamily := by
  intro hmax
  have heq := (full_maximizer_iff_eq opt hopt opt.toNodeFamily).1 hmax
  rw [canonical_allMinPeak_eq_one] at heq
  linarith

end
end JSPFreeNodes

-- Independent target type checks and real Lean axiom reports:
example : JSPFreeNodes.Target936 := JSPFreeNodes.jsp_000936
example : JSPFreeNodes.Target937Classification := JSPFreeNodes.jsp_000937_classification
#print axioms JSPFreeNodes.jsp_000936
#print axioms JSPFreeNodes.jsp_000937_classification
#print axioms JSPFreeNodes.canonical_allMinPeak_eq_one
#print axioms JSPFreeNodes.allMinPeak_le_any_amplification
