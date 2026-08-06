import RequestProject.Section31.Oscillation
import RequestProject.Section31.NoShortcut
import RequestProject.Section31.HarmonicSplines

/-!
# §3.1: the uniform contraction factor `θ ∈ (0,1)`, assembled

Reference: arXiv:2603.13798, §3.1, Lemma `lem:sec31_continuous_harmonics`.

The paper's sentence

> for each rule graph and each conductance vector from the compact family, the
> `0`–`1` harmonic profile has edge oscillation strictly smaller than `1`; since
> the family of rule graphs is finite, there is a uniform `θ ∈ (0,1)` such that
> every child-cell oscillation is at most `θ` times the parent-cell oscillation

is proved here in full, from the standing assumption of the paper.  The chain is:

1. Assumption `ass:standing` ⟹ no rule graph has an edge joining its two planting
   vertices (`IGS.Sec31.no_shortcut_of_distance_positive` for `K ≥ 2`,
   `IGS.Sec31.no_shortcut_of_two_le_dist` for `K = 1`);
2. no shortcut edge ⟹ every edge oscillation of the `0`–`1` profile is `< 1`
   (`IGS.Sec31.FiniteNetwork.edge_osc_lt_one_of_no_shortcut`, proved from the
   Euler–Lagrange equation, the truncation maximum principle and the strong
   maximum principle);
3. finitely many rule graphs ⟹ a single `θ < 1` (`exists_uniform_lt_one_of_finite'`);
4. affine dependence on the boundary data ⟹ the contraction of the oscillations
   from a cell to its children (`uniform_contraction_of_no_shortcut`);
5. `IGS.Sec31.osc_le_geometric` and
   `IGS.Sec31.exists_continuous_limit_of_geometric` then give
   `osc_n ≤ θ^n osc_0` and the continuous limit.

Step 3 for the *compact family of conductance vectors* (rather than for the
finitely many rule graphs) is `IGS.Sec31.exists_uniform_lt_one_of_tendsto`,
whose convergence hypothesis is supplied by `IGS.Sec31.tendsto_minimiser`.
-/

namespace IGS.Sec31

open Finset

/--
A finite family of reals all `< 1` admits a common bound `θ ∈ [0,1)`
(no nonemptiness needed: for an empty family take `θ = 0`).
-/
theorem exists_uniform_lt_one_of_finite' {ι : Type*} [Fintype ι] (osc : ι → ℝ)
    (h : ∀ i, osc i < 1) : ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ i, osc i ≤ θ := by
  classical
  by_cases hne : Nonempty ι
  · obtain ⟨i₀, -, hi₀⟩ :=
      Finset.exists_max_image (Finset.univ : Finset ι) osc ⟨Classical.arbitrary ι, mem_univ _⟩
    refine ⟨max 0 (osc i₀), le_max_left _ _, max_lt one_pos (h i₀), fun i => ?_⟩
    exact le_trans (hi₀ i (mem_univ i)) (le_max_right _ _)
  · exact ⟨0, le_refl _, one_pos, fun i => absurd ⟨i⟩ hne⟩

namespace FiniteNetwork

/--
**The uniform oscillation contraction of Lemma `sec31_continuous_harmonics`.**

`ι` indexes the (finitely many) pairs *(rule graph, admissible conductance
vector)*.  For each `i` we are given

* a finite network `net i` with two planting vertices `a i`, `b i`;
* a discrete Poincaré inequality with constant `K i` for functions vanishing at
  the planting vertices — this is what canonicality provides, see
  `IGS.Sec31.FiniteNetwork.poincare_of_path` — so that energy minimisers are
  unique;
* the `0`–`1` harmonic profile `g i` (the energy minimiser with boundary data
  `h i`, where `h i (a i) = 0` and `h i (b i) = 1`);
* **no shortcut edge**: no edge of `net i` joins `a i` to `b i`.

Then there is a single `θ ∈ [0,1)` such that, for *every* `i` and *every*
boundary datum, the minimiser `f` with values `c` at `a i` and `c + lam` at
`b i` satisfies

`|f(u) - f(v)| ≤ θ · |lam|` for every edge `{u,v}`,

i.e. the oscillation of the harmonic extension across any single edge of the
subdivided cell is at most `θ` times the oscillation `|lam|` of the datum across
the cell itself.
-/
theorem uniform_contraction_of_no_shortcut {ι : Type*} [Fintype ι]
    (V : ι → Type) [∀ i, DecidableEq (V i)] (net : ∀ i, FiniteNetwork (V i))
    (a b : ∀ i, V i) (K : ι → ℝ) (h g : ∀ i, V i → ℝ)
    (hP : ∀ i, ∀ f : V i → ℝ, (∀ x ∈ ({a i, b i} : Finset (V i)), f x = 0) →
      ∀ x, (f x) ^ 2 ≤ K i * (net i).energy f)
    (ha : ∀ i, h i (a i) = 0) (hb : ∀ i, h i (b i) = 1)
    (hbd : ∀ i, ∀ x ∈ ({a i, b i} : Finset (V i)), g i x = h i x)
    (hmin : ∀ i, ∀ f, (∀ x ∈ ({a i, b i} : Finset (V i)), f x = h i x) →
      (net i).energy (g i) ≤ (net i).energy f)
    (hns : ∀ i, ∀ e : (net i).Edge,
      ¬ ((((net i).ends e).1 = a i ∧ ((net i).ends e).2 = b i)
        ∨ (((net i).ends e).1 = b i ∧ ((net i).ends e).2 = a i))) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ (i : ι) (c lam : ℝ) (f : V i → ℝ),
      (∀ x ∈ ({a i, b i} : Finset (V i)), f x = c + lam * h i x) →
      (∀ f' : V i → ℝ, (∀ x ∈ ({a i, b i} : Finset (V i)), f' x = c + lam * h i x) →
        (net i).energy f ≤ (net i).energy f') →
      ∀ e : (net i).Edge, |f ((net i).ends e).1 - f ((net i).ends e).2| ≤ θ * |lam| := by
  classical
  -- step 2: each profile has all its edge oscillations `< 1`
  have hlt : ∀ (s : Σ i : ι, (net i).Edge),
      |g s.1 ((net s.1).ends s.2).1 - g s.1 ((net s.1).ends s.2).2| < 1 := by
    rintro ⟨i, e⟩
    exact (net i).edge_osc_lt_one_of_no_shortcut (a i) (b i) (K i) (h i) (hP i) (ha i) (hb i)
      (g i) (hbd i) (hmin i) (hns i) e
  -- step 3: a single `θ < 1` over the finite family
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := exists_uniform_lt_one_of_finite' _ hlt
  refine ⟨θ, hθ0, hθ1, fun i c lam f hfbd hfmin e => ?_⟩
  -- step 4: affine dependence on the boundary data
  have := (net i).edge_osc_le_mul_of_profile ({a i, b i} : Finset (V i)) (K i) θ (h i) (g i)
    (hP i) (hbd i) (hmin i) (fun e' => hθ ⟨i, e'⟩) c lam f hfbd hfmin e
  rw [mul_comm] at this
  exact this

end FiniteNetwork

/--
**Lemma `sec31_continuous_harmonics`, part (a), assembled.**

Given the uniform contraction factor `θ ∈ [0,1)` produced by
`FiniteNetwork.uniform_contraction_of_no_shortcut`, the level-`n` oscillations
of a harmonic extension decay geometrically, hence the extensions form a
uniformly Cauchy sequence and converge to a continuous function on the compact
limit space `Ξ_M`.

`osc n` is the largest oscillation of the extension over the level-`n` cells and
`u n` is the corresponding continuous interpolation; `hdist` is the (elementary)
comparison between the uniform distance of two consecutive interpolations and
the cell oscillation.
-/
theorem exists_continuous_limit_of_contraction
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (u : ℕ → C(X, ℝ)) (osc : ℕ → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hcon : ∀ n, osc (n + 1) ≤ θ * osc n)
    (hdist : ∀ n, dist (u n) (u (n + 1)) ≤ osc n) :
    ∃ w : C(X, ℝ), Filter.Tendsto u Filter.atTop (nhds w) ∧
      TendstoUniformly (fun n => (u n : X → ℝ)) w Filter.atTop := by
  refine exists_continuous_limit_of_geometric u (osc 0) θ hθ1 fun n => ?_
  exact le_trans (hdist n) (by simpa [mul_comm] using osc_le_geometric osc θ hθ0 hcon n)

end IGS.Sec31
