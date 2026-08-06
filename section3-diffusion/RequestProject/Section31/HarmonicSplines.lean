import Mathlib

/-!
# §3.1, step 2: continuous harmonic splines (Lemma `sec31_continuous_harmonics`)

Reference: arXiv:2603.13798, §3.1, Lemma `sec31_continuous_harmonics`.

The lemma has two halves.

**(a) Existence of the continuous extension.**  The harmonic extensions of a
fixed `h : V(Ξ^m) → ℝ` to the deeper levels form a sequence whose consecutive
differences are controlled by the cell oscillations, and the paper's key input
is a *uniform oscillation contraction*: there is `θ ∈ (0,1)`, depending only on
the finite family of rule graphs and on the compact family of admissible
conductance vectors, such that the oscillation of the extension on a child cell
is at most `θ` times its oscillation on the parent cell.  Hence
`osc_n ≤ θ^n osc_0`, the sequence is uniformly Cauchy, and (the domain being
compact) it converges uniformly to a continuous function on `Ξ_M`.

`osc_le_geometric` is the contraction bookkeeping and
`exists_continuous_limit_of_geometric` the completeness argument; the conclusion
is stated both as convergence in `C(Ξ_M, ℝ)` and as uniform convergence.

**(b) Density.**  Given `f ∈ C(Ξ_M)` and `ε > 0`, choose `m` with oscillation of
`f` at most `ε` on every level-`m` cell.  The harmonic extension `g` of
`f|_{V(Ξ^m)}` obeys the maximum principle: on each level-`m` cell its values lie
between two values of `f` on that cell.  Hence `‖f - g‖_∞ ≤ ε`.
`dist_le_of_cellwise_maximum_principle` is exactly this step and
`dense_of_approx` turns it into density.

The uniform contraction factor `θ < 1` and the maximum principle for harmonic
extensions enter the statements below as parameters; both are *proved* from the
standing assumption of the paper in `RequestProject/Section31/Oscillation.lean`
and `RequestProject/Section31/Contraction.lean` (the maximum principle in
`range_subset_of_min`, the contraction in `uniform_contraction_of_no_shortcut`),
so nothing here is left to the reader.
-/

namespace IGS.Sec31

open Filter Topology

/--
**Geometric decay of the cell oscillations.**
The uniform contraction `osc (n+1) ≤ θ * osc n` gives `osc n ≤ θ^n * osc 0`.
-/
theorem osc_le_geometric (osc : ℕ → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hcon : ∀ n, osc (n + 1) ≤ θ * osc n) :
    ∀ n, osc n ≤ θ ^ n * osc 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      calc osc (k + 1) ≤ θ * osc k := hcon k
        _ ≤ θ * (θ ^ k * osc 0) := by
            have := mul_le_mul_of_nonneg_left ih hθ0
            simpa using this
        _ = θ ^ (k + 1) * osc 0 := by ring

/--
**Lemma `sec31_continuous_harmonics`, part (a).**
A sequence of continuous functions on a compact space whose consecutive
distances decay geometrically converges uniformly to a continuous function.
This is the statement that the harmonic extensions of a fixed level-`m` boundary
datum define a unique continuous function on `Ξ_M`.
-/
theorem exists_continuous_limit_of_geometric
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (u : ℕ → C(X, ℝ)) (K θ : ℝ)
    (hθ : θ < 1) (h : ∀ n, dist (u n) (u (n + 1)) ≤ K * θ ^ n) :
    ∃ w : C(X, ℝ), Tendsto u atTop (𝓝 w) ∧
      TendstoUniformly (fun n => (u n : X → ℝ)) w atTop := by
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric θ K hθ h)
  exact ⟨w, hw, ContinuousMap.tendsto_iff_tendstoUniformly.mp hw⟩

/--
**Maximum principle ⟹ uniform `ε`-approximation (Lemma `sec31_continuous_harmonics`,
part (b)).**

`cell x` is the level-`m` cell containing `x`; `hosc` says that `f` oscillates by
at most `ε` on each cell, and `hbetween` is the maximum principle for the
harmonic extension `g`: its value at `x` lies between two values of `f` on the
cell of `x` (namely the two terminal values).  Then `|f x - g x| ≤ ε` everywhere.
-/
theorem dist_le_of_cellwise_maximum_principle
    {X : Type*} (f g : X → ℝ) (cell : X → Set X) (ε : ℝ)
    (hmem : ∀ x, x ∈ cell x)
    (hosc : ∀ x, ∀ y ∈ cell x, ∀ z ∈ cell x, |f y - f z| ≤ ε)
    (hbetween : ∀ x, ∃ y ∈ cell x, ∃ z ∈ cell x, f y ≤ g x ∧ g x ≤ f z) :
    ∀ x, |f x - g x| ≤ ε := by
  intro x
  obtain ⟨y, hy, z, hz, hyg, hgz⟩ := hbetween x
  have h1 : |f x - f y| ≤ ε := hosc x x (hmem x) y hy
  have h2 : |f x - f z| ≤ ε := hosc x x (hmem x) z hz
  rw [abs_le] at h1 h2 ⊢
  constructor <;> [linarith [h2.1]; linarith [h1.2]]

/--
**Density from uniform approximation.**
If every point of a metric space can be approximated arbitrarily well by
elements of `S`, then `S` is dense.  Combined with the previous lemma this is
the second assertion of Lemma `sec31_continuous_harmonics`: the union of the
spaces `ℋ_m` of continuous harmonic splines is uniformly dense in `C(Ξ_M)`.
-/
theorem dense_of_approx {X : Type*} [MetricSpace X] (S : Set X)
    (h : ∀ x : X, ∀ ε > 0, ∃ g ∈ S, dist x g ≤ ε) : Dense S := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨g, hg, hd⟩ := h x (r / 2) (by linarith)
  exact ⟨g, by simpa [Metric.mem_ball, dist_comm] using lt_of_le_of_lt hd (by linarith), hg⟩

/--
**Lemma `sec31_continuous_harmonics`, part (b), assembled.**
If for every `f ∈ C(X)` and every `ε > 0` the set `S` of harmonic splines
contains a `g` with `|f x - g x| ≤ ε` for all `x`, then `S` is dense in `C(X)`
for the uniform norm.
-/
theorem dense_of_cellwise_approx {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (S : Set C(X, ℝ))
    (h : ∀ (f : C(X, ℝ)), ∀ ε > 0, ∃ g ∈ S, ∀ x, |f x - g x| ≤ ε) : Dense S := by
  refine dense_of_approx S fun f ε hε => ?_
  obtain ⟨g, hg, hgf⟩ := h f (ε / 2) (by linarith)
  refine ⟨g, hg, ?_⟩
  have : dist f g ≤ ε / 2 := by
    refine (ContinuousMap.dist_le (by linarith)).2 fun x => ?_
    simpa [Real.dist_eq] using hgf x
  linarith

end IGS.Sec31
