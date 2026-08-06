import Mathlib

/-!
# The Dirichlet principle on a finite network

This file supplies, from scratch, the finite-network input of Lemma
`sec31_trace_weighted` of arXiv:2603.13798: *on a finite network, the energy
minimisation problem with prescribed boundary values has a solution, and the
solution is unique*.  In §3.1 this is applied on a single copy of a rule graph
`R_i`, whose two planting vertices carry the prescribed values; the paper cites
`kigami2001analysis` for it.  Here it is proved.

The only analytic input is a discrete Poincaré inequality
`(g x)² ≤ K ℰ(g)` for functions vanishing on the boundary set `V₀`; this is
exactly what connectivity of the network to `V₀` provides, and
`poincare_of_path` derives it from a path of length `L` joining `x` to `V₀`
(with distinct edges), with the explicit constant `K = L / c_min`.  For an EIGS
rule graph, canonicality (every edge lies on a simple path between the two
planting vertices) gives such paths.

The statements:

* `poincare_of_path` — the discrete Poincaré inequality along a path;
* `exists_min` — existence of an energy minimiser with prescribed values on
  `V₀` (Dirichlet principle);
* `min_unique` — uniqueness of the minimiser, via the parallelogram identity
  for the energy and the Poincaré inequality.
-/

namespace IGS.Sec31

open Finset Metric

/-- A finite network: a finite set of edges with endpoints and positive conductances. -/
structure FiniteNetwork (V : Type*) where
  /-- the (finite) edge set -/
  Edge : Type
  fintypeEdge : Fintype Edge
  decEqEdge : DecidableEq Edge
  /-- the two endpoints of an edge -/
  ends : Edge → V × V
  /-- the conductance of an edge -/
  cond : Edge → ℝ
  cond_pos : ∀ e, 0 < cond e

attribute [instance] FiniteNetwork.fintypeEdge FiniteNetwork.decEqEdge

namespace FiniteNetwork

variable {V : Type*} (net : FiniteNetwork V)

/-- The Dirichlet energy `ℰ(g) = ∑_e c_e (g(a_e) - g(b_e))²`. -/
noncomputable def energy (g : V → ℝ) : ℝ :=
  ∑ e, net.cond e * (g (net.ends e).1 - g (net.ends e).2) ^ 2

theorem energy_nonneg (g : V → ℝ) : 0 ≤ net.energy g :=
  Finset.sum_nonneg fun e _ => by have := net.cond_pos e; positivity

theorem energy_continuous [Fintype V] : Continuous net.energy := by
  unfold energy; fun_prop

/-- `ℰ(g₁ - g₂) ≤ 2ℰ(g₁) + 2ℰ(g₂)`. -/
theorem energy_sub_le (g1 g2 : V → ℝ) :
    net.energy (fun x => g1 x - g2 x) ≤ 2 * net.energy g1 + 2 * net.energy g2 := by
  unfold energy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have hc := (net.cond_pos e).le
  nlinarith [sq_nonneg (g1 (net.ends e).1 - g1 (net.ends e).2
      + (g2 (net.ends e).1 - g2 (net.ends e).2)),
    sq_nonneg (g1 (net.ends e).1 - g1 (net.ends e).2
      - (g2 (net.ends e).1 - g2 (net.ends e).2))]

/-- The parallelogram identity for the energy. -/
theorem energy_parallelogram (g1 g2 : V → ℝ) :
    net.energy g1 + net.energy g2
      = 2 * net.energy (fun x => (g1 x + g2 x) / 2)
        + 2 * net.energy (fun x => (g1 x - g2 x) / 2) := by
  simp only [energy, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/--
**Discrete Poincaré inequality.**
If `g` vanishes on `V₀`, if `v 0 = x`, `v L ∈ V₀`, and the consecutive vertices
`v i`, `v (i+1)` are the endpoints of the (distinct) edges `e i`, then
`(g x)² ≤ (L / c_min) ℰ(g)`.
-/
theorem poincare_of_path (V₀ : Finset V) (cmin : ℝ) (hcmin : 0 < cmin)
    (hc : ∀ e, cmin ≤ net.cond e) (g : V → ℝ) (hg : ∀ x ∈ V₀, g x = 0)
    (x : V) (L : ℕ) (v : ℕ → V) (e : ℕ → net.Edge)
    (hv0 : v 0 = x) (hvL : v L ∈ V₀)
    (hstep : ∀ i ∈ range L, (g (v i) - g (v (i + 1))) ^ 2
        = (g (net.ends (e i)).1 - g (net.ends (e i)).2) ^ 2)
    (hinj : Set.InjOn e (range L : Finset ℕ)) :
    (g x) ^ 2 ≤ (L / cmin) * net.energy g := by
  have htel : ∑ i ∈ range L, (g (v i) - g (v (i + 1))) = g x := by
    rw [Finset.sum_range_sub' (fun i => g (v i)) L, hv0, hg (v L) hvL, sub_zero]
  have hcs : (g x) ^ 2 ≤ L * ∑ i ∈ range L, (g (v i) - g (v (i + 1))) ^ 2 := by
    rw [← htel]
    simpa using sq_sum_le_card_mul_sum_sq (s := range L) (f := fun i => g (v i) - g (v (i + 1)))
  have hrw : ∑ i ∈ range L, (g (v i) - g (v (i + 1))) ^ 2
      = ∑ i ∈ range L, (g (net.ends (e i)).1 - g (net.ends (e i)).2) ^ 2 :=
    Finset.sum_congr rfl hstep
  have hbound : ∑ i ∈ range L, (g (net.ends (e i)).1 - g (net.ends (e i)).2) ^ 2
      ≤ (1 / cmin) * net.energy g := by
    have h1 : ∀ i ∈ range L, (g (net.ends (e i)).1 - g (net.ends (e i)).2) ^ 2
        ≤ (1 / cmin) * (net.cond (e i) * (g (net.ends (e i)).1 - g (net.ends (e i)).2) ^ 2) := by
      intro i _
      set c := net.cond (e i)
      set d := (g (net.ends (e i)).1 - g (net.ends (e i)).2) ^ 2 with hd
      have hci : cmin ≤ c := hc (e i)
      have hd0 : 0 ≤ d := by rw [hd]; positivity
      have key : 1 / cmin * (c * d) - d = ((c - cmin) / cmin) * d := by field_simp
      have h2 : 0 ≤ ((c - cmin) / cmin) * d :=
        mul_nonneg (div_nonneg (by linarith) hcmin.le) hd0
      linarith
    have hsub : ∑ i ∈ range L,
        net.cond (e i) * (g (net.ends (e i)).1 - g (net.ends (e i)).2) ^ 2 ≤ net.energy g := by
      unfold energy
      rw [← Finset.sum_image
        (f := fun a => net.cond a * (g (net.ends a).1 - g (net.ends a).2) ^ 2) hinj]
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ => ?_
      have := (net.cond_pos a).le
      positivity
    have hinvpos : (0 : ℝ) ≤ 1 / cmin := by positivity
    calc ∑ i ∈ range L, (g (net.ends (e i)).1 - g (net.ends (e i)).2) ^ 2
        ≤ ∑ i ∈ range L,
            (1 / cmin) * (net.cond (e i) * (g (net.ends (e i)).1 - g (net.ends (e i)).2) ^ 2) :=
          Finset.sum_le_sum h1
      _ = (1 / cmin) * ∑ i ∈ range L,
            net.cond (e i) * (g (net.ends (e i)).1 - g (net.ends (e i)).2) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (1 / cmin) * net.energy g := by nlinarith
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  calc (g x) ^ 2 ≤ L * ∑ i ∈ range L, (g (v i) - g (v (i + 1))) ^ 2 := hcs
    _ = L * ∑ i ∈ range L, (g (net.ends (e i)).1 - g (net.ends (e i)).2) ^ 2 := by rw [hrw]
    _ ≤ L * ((1 / cmin) * net.energy g) := by nlinarith
    _ = (L / cmin) * net.energy g := by ring

variable [Fintype V]

/--
**The Dirichlet principle: existence.**
Given a discrete Poincaré inequality with constant `K` for functions vanishing
on `V₀`, the energy attains its minimum on the affine set of functions equal to
`h` on `V₀`.
-/
theorem exists_min (V₀ : Finset V) (h : V → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hP : ∀ g : V → ℝ, (∀ x ∈ V₀, g x = 0) → ∀ x, (g x) ^ 2 ≤ K * net.energy g) :
    ∃ g₀, (∀ x ∈ V₀, g₀ x = h x) ∧
      ∀ g, (∀ x ∈ V₀, g x = h x) → net.energy g₀ ≤ net.energy g := by
  classical
  set M := net.energy h with hM
  set T : Set (V → ℝ) := {g | (∀ x ∈ V₀, g x = h x) ∧ net.energy g ≤ M} with hT
  have hMnn : 0 ≤ M := net.energy_nonneg h
  have hTne : T.Nonempty := ⟨h, fun x _ => rfl, le_refl _⟩
  have hTclosed : IsClosed T := by
    have h1 : IsClosed {g : V → ℝ | ∀ x ∈ V₀, g x = h x} := by
      have hEq : {g : V → ℝ | ∀ x ∈ V₀, g x = h x} = ⋂ x ∈ V₀, {g : V → ℝ | g x = h x} := by
        ext g; simp [Set.mem_iInter]
      rw [hEq]
      exact isClosed_biInter fun x _ => isClosed_eq (continuous_apply x) continuous_const
    exact h1.inter (isClosed_le net.energy_continuous continuous_const)
  have hbound : T ⊆ closedBall h (2 * Real.sqrt (K * M)) := by
    intro g hg
    have hd : ∀ x ∈ V₀, (g x - h x) = 0 := fun x hx => by rw [hg.1 x hx]; ring
    have hE : net.energy (fun x => g x - h x) ≤ 4 * M := by
      have h1 := net.energy_sub_le g h
      have h2 : net.energy g ≤ M := hg.2
      linarith
    have hpt : ∀ x, |g x - h x| ≤ 2 * Real.sqrt (K * M) := by
      intro x
      have h1 := hP (fun x => g x - h x) hd x
      have h2 : (g x - h x) ^ 2 ≤ K * (4 * M) :=
        le_trans h1 (mul_le_mul_of_nonneg_left hE hK)
      have h3 : |g x - h x| ≤ Real.sqrt (K * (4 * M)) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt h2
      have h4 : Real.sqrt (K * (4 * M)) = 2 * Real.sqrt (K * M) := by
        rw [show K * (4 * M) = 4 * (K * M) by ring, Real.sqrt_mul (by norm_num),
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith [h4 ▸ h3]
    rw [mem_closedBall, dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun x => ?_
    simpa [Real.norm_eq_abs] using hpt x
  have hTcompact : IsCompact T :=
    Metric.isCompact_of_isClosed_isBounded hTclosed (Metric.isBounded_closedBall.subset hbound)
  obtain ⟨g₀, hg₀T, hg₀min⟩ := hTcompact.exists_isMinOn hTne net.energy_continuous.continuousOn
  refine ⟨g₀, hg₀T.1, fun g hg => ?_⟩
  by_cases hgM : net.energy g ≤ M
  · exact hg₀min ⟨hg, hgM⟩
  · exact le_trans hg₀T.2 (le_of_lt (not_le.mp hgM))

omit [Fintype V] in
/--
**The Dirichlet principle: uniqueness.**
Two minimisers with the same boundary values coincide.  The proof is the
parallelogram identity — the midpoint is admissible, so the half-difference has
zero energy — followed by the Poincaré inequality.
-/
theorem min_unique (V₀ : Finset V) (h : V → ℝ) (K : ℝ)
    (hP : ∀ g : V → ℝ, (∀ x ∈ V₀, g x = 0) → ∀ x, (g x) ^ 2 ≤ K * net.energy g)
    (g1 g2 : V → ℝ) (h1 : ∀ x ∈ V₀, g1 x = h x) (h2 : ∀ x ∈ V₀, g2 x = h x)
    (hmin1 : ∀ g, (∀ x ∈ V₀, g x = h x) → net.energy g1 ≤ net.energy g)
    (hmin2 : ∀ g, (∀ x ∈ V₀, g x = h x) → net.energy g2 ≤ net.energy g) :
    g1 = g2 := by
  have hmid : ∀ x ∈ V₀, (fun x => (g1 x + g2 x) / 2) x = h x := by
    intro x hx; simp [h1 x hx, h2 x hx]
  have heq : net.energy g1 = net.energy g2 :=
    le_antisymm (hmin1 g2 h2) (hmin2 g1 h1)
  have hpar := net.energy_parallelogram g1 g2
  have hmidmin : net.energy g1 ≤ net.energy (fun x => (g1 x + g2 x) / 2) := hmin1 _ hmid
  have hdiff0 : net.energy (fun x => (g1 x - g2 x) / 2) ≤ 0 := by linarith
  have hdiffge : 0 ≤ net.energy (fun x => (g1 x - g2 x) / 2) :=
    net.energy_nonneg _
  have hdiff : net.energy (fun x => (g1 x - g2 x) / 2) = 0 := le_antisymm hdiff0 hdiffge
  have hvan : ∀ x ∈ V₀, (fun x => (g1 x - g2 x) / 2) x = 0 := by
    intro x hx; simp [h1 x hx, h2 x hx]
  funext x
  have hsq := hP (fun x => (g1 x - g2 x) / 2) hvan x
  rw [hdiff, mul_zero] at hsq
  have : ((g1 x - g2 x) / 2) = 0 := by nlinarith [sq_nonneg ((g1 x - g2 x) / 2)]
  linarith [this]

end FiniteNetwork

end IGS.Sec31
