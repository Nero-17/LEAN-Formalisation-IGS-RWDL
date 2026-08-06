import Mathlib

/-!
# No shortcut edges (Assumption `ass:standing` of arXiv:2603.13798)

`SECTION31_NOTES.md` flagged one point of §3.1 as apparently needing an extra
hypothesis: the uniform oscillation contraction in Lemma
`lem:sec31_continuous_harmonics` fails for a rule graph containing a **shortcut
edge**, i.e. an edge joining the two planting vertices `β_i^+`, `β_i^-`
directly, because the `0`–`1` harmonic profile then has oscillation exactly `1`
across that edge.

This file shows that the standing assumption of the paper already rules such
edges out, so that no extra hypothesis is needed after all.  Assumption
`ass:standing`(2) has two clauses, and the two clauses cover the two cases:

* **`K ≥ 2`, distance-positivity.**  The path-selection family `𝒟` of
  \[neroli2024fractal\] collects, for every choice of a simple `β_i^+`–`β_i^-`
  path in each rule graph, the matrix whose `(i,j)` entry counts the colour-`j`
  edges of the chosen path in `R_i`.  Distance-positivity says that *every*
  matrix in `𝒟` is (entrywise) positive, i.e. every selectable path uses every
  colour at least once.  A shortcut edge would provide a path whose colour
  vector is the singleton `{c}`, which misses every colour other than `c`; with
  at least two colours this contradicts positivity.  This is
  `no_shortcut_of_distance_positive`.

* **`K = 1`.**  Here the assumption is imposed directly:
  `d(β_1^+, β_1^-) ≥ 2`, and an edge between the planting vertices would make
  the distance `1`.  This is `no_shortcut_of_two_le_dist`.

The file also contains the two elementary "uniformity" statements that turn the
strict inequality `osc < 1` of `IGS.Sec31.FiniteNetwork.edge_osc_lt_one_of_no_shortcut`
into the *uniform* contraction factor `θ ∈ (0,1)` the paper uses: a maximum over
a finite family (`exists_uniform_lt_one_of_finite`, the finitely many rule
graphs) and a supremum over a convergent family (`exists_uniform_lt_one_of_tendsto`,
the compact family of conductance vectors `α^{(q)} → α^{(∞)}`, whose profiles
converge by `IGS.Sec31.tendsto_minimiser`).
-/

namespace IGS.Sec31

open Finset

/--
**Distance-positivity excludes shortcut edges when there are at least two
colours.**

`Paths i` is the set of colour-count vectors (as multisets of colours) of the
selectable simple `β_i^+`–`β_i^-` paths of the rule graph `R_i`; `hne` says that
each rule graph has at least one such path (connectivity), and `hpos` is
distance-positivity: for every selection `p` of one path per rule graph, every
colour occurs in every selected path.  Then no rule graph has a shortcut edge:
the singleton colour vector `{c}` — the colour vector of a single edge joining
the two planting vertices — is not the vector of a selectable path.
-/
theorem no_shortcut_of_distance_positive {ι : Type*} [DecidableEq ι] [Fintype ι]
    (Paths : ι → Set (Multiset ι)) (hne : ∀ i, (Paths i).Nonempty)
    (hpos : ∀ p : ι → Multiset ι, (∀ i, p i ∈ Paths i) → ∀ i j, j ∈ p i)
    (hK : 2 ≤ Fintype.card ι) (i c : ι) : ({c} : Multiset ι) ∉ Paths i := by
  intro hmem
  classical
  set p : ι → Multiset ι := fun k => if k = i then {c} else (hne k).choose with hp
  have hpmem : ∀ k, p k ∈ Paths k := by
    intro k
    by_cases hk : k = i
    · subst hk; simpa [hp] using hmem
    · simpa [hp, hk] using (hne k).choose_spec
  -- every colour occurs in the singleton `{c}`, so every colour equals `c`
  have hall : ∀ j : ι, j = c := by
    intro j
    have := hpos p hpmem i j
    have hpi : p i = ({c} : Multiset ι) := by simp [hp]
    rw [hpi] at this
    simpa using this
  -- but there are at least two colours
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) c
  exact hj (hall j)

/--
**The `K = 1` clause of the standing assumption excludes shortcut edges.**
If the two planting vertices are at graph distance at least `2`, they are not
adjacent.
-/
theorem no_shortcut_of_two_le_dist {V : Type*} (G : SimpleGraph V) (a b : V)
    (h : 2 ≤ G.dist a b) : ¬ G.Adj a b := by
  intro hadj
  have h1 : G.dist a b = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hadj
  omega

/--
**Uniformity over the finitely many rule graphs.**
If a nonempty finite family of oscillations is bounded by `1` strictly, a single
`θ < 1` bounds them all.
-/
theorem exists_uniform_lt_one_of_finite {ι : Type*} [Fintype ι] [Nonempty ι] (osc : ι → ℝ)
    (h : ∀ i, osc i < 1) : ∃ θ : ℝ, θ < 1 ∧ ∀ i, osc i ≤ θ := by
  classical
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset ι) osc ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  exact ⟨osc i₀, h i₀, fun i => hi₀ i (Finset.mem_univ i)⟩

/--
**Uniformity over the compact family of conductance vectors.**
The admissible conductance vectors form the sequence `α^{(q)}` together with its
limit `α^{(∞)}`.  If the corresponding oscillations are all `< 1` and converge to
the oscillation of the limit (which is `< 1`), then a single `θ < 1` bounds the
whole family.
-/
theorem exists_uniform_lt_one_of_tendsto (osc : ℕ → ℝ) (oscinf : ℝ)
    (hconv : Filter.Tendsto osc Filter.atTop (nhds oscinf))
    (h : ∀ q, osc q < 1) (hinf : oscinf < 1) :
    ∃ θ : ℝ, θ < 1 ∧ (∀ q, osc q ≤ θ) ∧ oscinf ≤ θ := by
  classical
  -- beyond some `N` the oscillations are below `(1 + oscinf)/2`
  set b : ℝ := (1 + oscinf) / 2 with hb
  have hb1 : b < 1 := by rw [hb]; linarith
  have hbinf : oscinf < b := by rw [hb]; linarith
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop).1 (hconv.eventually (eventually_lt_nhds hbinf))
  -- the finitely many remaining ones are handled by a maximum
  set S : Finset ℕ := Finset.range N with hS
  by_cases hSne : S.Nonempty
  · obtain ⟨q₀, -, hq₀⟩ := Finset.exists_max_image S osc hSne
    refine ⟨max b (osc q₀), max_lt hb1 (h q₀), fun q => ?_, le_trans hbinf.le (le_max_left _ _)⟩
    by_cases hq : q < N
    · exact le_trans (hq₀ q (by simpa [hS] using hq)) (le_max_right _ _)
    · exact le_trans (hN q (by omega)).le (le_max_left _ _)
  · refine ⟨b, hb1, fun q => ?_, hbinf.le⟩
    have hN0 : N = 0 := by
      by_contra hcon
      exact hSne ⟨0, by simp [hS]; omega⟩
    exact (hN q (by omega)).le

end IGS.Sec31
