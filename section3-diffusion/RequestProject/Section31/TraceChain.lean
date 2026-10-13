import RequestProject.Section31.WatchedChain

/-!
# The traced (watched) chain on the skeleton

Reference: arXiv:2603.13798, §3.1, proof of Lemma 3.11: *"Observed at successive
distinct skeleton vertices, the walk is the random walk on the rule graph in
which every colour-`j` edge carries the effective conductance of the
corresponding `(s-1)`-step copy, by the super-edge reduction underlying
Lemma 2.4."*

This file proves the part of that sentence that does not depend on §2, namely
that **the watched process is a Markov chain on the skeleton**: the hitting
distribution of the skeleton `S` is well defined (`hitDistLim`, a monotone limit
of the `k`-step hitting distributions), it is supported on `S`, and — as soon as
the walk hits `S` almost surely, which on a finite state space is guaranteed by
the uniform hitting estimates of `WatchedChain` — it is a probability
distribution.  Consequently

  `traceChain : FinChain ↥S`,   `Q(v,w) = ∑_u P(v,u) · P_u(X_{σ_S} = w)`,

is a genuine transition kernel on the skeleton, to which every result of
`WatchedChain` applies.

What remains from §2 is only the *identification* of this kernel with the
conductance walk on the rule graph whose colour-`j` conductances are the
effective conductances of the `(s-1)`-step copies (Lemma 2.4, Corollary 2.8).
-/

namespace IGS.Sec31

open Finset Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `hitDist ch S k v w` is the probability that the chain started at `v` is at
`w` when it first visits `S`, and that this happens within `k` steps. -/
def hitDist (ch : FinChain V) (S : Finset V) : ℕ → V → V → ℝ
  | 0, v, w => if v ∈ S then (if v = w then 1 else 0) else 0
  | (k + 1), v, w =>
      if v ∈ S then (if v = w then 1 else 0) else ∑ u, ch.P v u * hitDist ch S k u w

section Basic

variable (ch : FinChain V) (S : Finset V)

theorem hitDist_nonneg : ∀ (k : ℕ) (v w : V), 0 ≤ hitDist ch S k v w
  | 0, v, w => by
      unfold hitDist; split_ifs <;> norm_num
  | (k + 1), v, w => by
      unfold hitDist
      split_ifs
      · norm_num
      · norm_num
      · exact sum_nonneg fun u _ => mul_nonneg (ch.P_nonneg v u) (hitDist_nonneg k u w)

/-- The hitting distribution is supported on the skeleton. -/
theorem hitDist_eq_zero_of_not_mem {w : V} (hw : w ∉ S) :
    ∀ (k : ℕ) (v : V), hitDist ch S k v w = 0
  | 0, v => by
      by_cases hv : v ∈ S
      · have : v ≠ w := fun h => hw (h ▸ hv)
        simp [hitDist, hv, this]
      · simp [hitDist, hv]
  | (k + 1), v => by
      by_cases hv : v ∈ S
      · have : v ≠ w := fun h => hw (h ▸ hv)
        simp [hitDist, hv, this]
      · simp only [hitDist, hv, if_false]
        exact sum_eq_zero fun u _ => by rw [hitDist_eq_zero_of_not_mem hw k u]; ring

/-- Total mass: the chain is at some skeleton point at the hitting time exactly
when it has hit `S`. -/
theorem hitDist_sum : ∀ (k : ℕ) (v : V),
    ∑ w, hitDist ch S k v w = 1 - notHit ch S k v
  | 0, v => by
      by_cases hv : v ∈ S
      · simp [hitDist, notHit, hv]
      · simp [hitDist, notHit, hv]
  | (k + 1), v => by
      by_cases hv : v ∈ S
      · simp [hitDist, notHit, hv]
      · simp only [hitDist, notHit, hv, if_false]
        calc ∑ w, ∑ u, ch.P v u * hitDist ch S k u w
            = ∑ u, ∑ w, ch.P v u * hitDist ch S k u w := Finset.sum_comm
          _ = ∑ u, ch.P v u * (1 - notHit ch S k u) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [← Finset.mul_sum, hitDist_sum k u]
          _ = 1 - ∑ u, ch.P v u * notHit ch S k u := by
              have hs : ∑ u, ch.P v u * (1 - notHit ch S k u)
                  = (∑ u, ch.P v u) - ∑ u, ch.P v u * notHit ch S k u := by
                rw [← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun u _ => by ring
              rw [hs, ch.P_sum v]

theorem hitDist_le_one (k : ℕ) (v w : V) : hitDist ch S k v w ≤ 1 := by
  have h1 : hitDist ch S k v w ≤ ∑ w', hitDist ch S k v w' :=
    Finset.single_le_sum (fun w' _ => hitDist_nonneg ch S k v w') (mem_univ w)
  have h2 : ∑ w', hitDist ch S k v w' = 1 - notHit ch S k v := hitDist_sum ch S k v
  have h3 : 0 ≤ notHit ch S k v := notHit_nonneg ch S k v
  linarith

theorem hitDist_le_succ : ∀ (k : ℕ) (v w : V),
    hitDist ch S k v w ≤ hitDist ch S (k + 1) v w
  | 0, v, w => by
      by_cases hv : v ∈ S
      · show (if v ∈ S then (if v = w then (1:ℝ) else 0) else 0)
            ≤ if v ∈ S then (if v = w then (1:ℝ) else 0) else _
        rw [if_pos hv, if_pos hv]
      · show (if v ∈ S then (if v = w then (1:ℝ) else 0) else 0)
            ≤ if v ∈ S then (if v = w then (1:ℝ) else 0)
              else ∑ u, ch.P v u * hitDist ch S 0 u w
        rw [if_neg hv, if_neg hv]
        exact sum_nonneg fun u _ => mul_nonneg (ch.P_nonneg v u) (hitDist_nonneg ch S 0 u w)
  | (k + 1), v, w => by
      by_cases hv : v ∈ S
      · show (if v ∈ S then (if v = w then (1:ℝ) else 0) else _)
            ≤ if v ∈ S then (if v = w then (1:ℝ) else 0) else _
        rw [if_pos hv, if_pos hv]
      · show (if v ∈ S then (if v = w then (1:ℝ) else 0)
              else ∑ u, ch.P v u * hitDist ch S k u w)
            ≤ if v ∈ S then (if v = w then (1:ℝ) else 0)
              else ∑ u, ch.P v u * hitDist ch S (k + 1) u w
        rw [if_neg hv, if_neg hv]
        exact sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_left (hitDist_le_succ k u w) (ch.P_nonneg v u)

theorem hitDist_monotone (v w : V) : Monotone fun k => hitDist ch S k v w :=
  monotone_nat_of_le_succ fun k => hitDist_le_succ ch S k v w

/-- The hitting distribution of the skeleton, `P_v(X_{σ_S} = w)`. -/
noncomputable def hitDistLim (ch : FinChain V) (S : Finset V) (v w : V) : ℝ :=
  ⨆ k : ℕ, hitDist ch S k v w

theorem hitDist_tendsto (v w : V) :
    Tendsto (fun k => hitDist ch S k v w) atTop (𝓝 (hitDistLim ch S v w)) :=
  tendsto_atTop_ciSup (hitDist_monotone ch S v w) ⟨1, by rintro _ ⟨k, rfl⟩; exact hitDist_le_one ch S k v w⟩

theorem hitDistLim_nonneg (v w : V) : 0 ≤ hitDistLim ch S v w :=
  le_ciSup_of_le ⟨1, by rintro _ ⟨k, rfl⟩; exact hitDist_le_one ch S k v w⟩ 0
    (hitDist_nonneg ch S 0 v w)

theorem hitDistLim_eq_zero_of_not_mem {w : V} (hw : w ∉ S) (v : V) :
    hitDistLim ch S v w = 0 := by
  have : ∀ k : ℕ, hitDist ch S k v w = 0 := fun k => hitDist_eq_zero_of_not_mem ch S hw k v
  simp [hitDistLim, this]

/--
**The hitting distribution is a probability distribution** as soon as the
skeleton is hit almost surely.
-/
theorem hitDistLim_sum (hS : ∀ v, Tendsto (fun k => notHit ch S k v) atTop (𝓝 0)) (v : V) :
    ∑ w, hitDistLim ch S v w = 1 := by
  have h1 : Tendsto (fun k => ∑ w, hitDist ch S k v w) atTop (𝓝 (∑ w, hitDistLim ch S v w)) :=
    tendsto_finset_sum _ fun w _ => hitDist_tendsto ch S v w
  have h2 : Tendsto (fun k => ∑ w, hitDist ch S k v w) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ))).sub (hS v)
    simpa [hitDist_sum ch S] using this
  exact tendsto_nhds_unique h1 h2

theorem hitDistLim_sum_le_one (v : V) : ∑ w, hitDistLim ch S v w ≤ 1 := by
  have h1 : Tendsto (fun k => ∑ w, hitDist ch S k v w) atTop (𝓝 (∑ w, hitDistLim ch S v w)) :=
    tendsto_finset_sum _ fun w _ => hitDist_tendsto ch S v w
  refine le_of_tendsto h1 (Filter.Eventually.of_forall fun k => ?_)
  rw [hitDist_sum ch S k v]
  linarith [notHit_nonneg ch S k v]

/-- At a skeleton point the hitting distribution is the Dirac mass. -/
theorem hitDist_of_mem {v : V} (hv : v ∈ S) :
    ∀ (k : ℕ) (w : V), hitDist ch S k v w = if v = w then 1 else 0
  | 0, w => by simp [hitDist, hv]
  | (_ + 1), w => by simp [hitDist, hv]

theorem hitDistLim_of_mem {v : V} (hv : v ∈ S) (w : V) :
    hitDistLim ch S v w = if v = w then 1 else 0 := by
  simp [hitDistLim, hitDist_of_mem ch S hv]

/-- Off the skeleton, the hitting distribution satisfies the first-step
recursion. -/
theorem hitDistLim_succ {v : V} (hv : v ∉ S) (w : V) :
    hitDistLim ch S v w = ∑ u, ch.P v u * hitDistLim ch S u w := by
  have h1 : Tendsto (fun k => hitDist ch S (k + 1) v w) atTop (𝓝 (hitDistLim ch S v w)) :=
    (hitDist_tendsto ch S v w).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k => ∑ u, ch.P v u * hitDist ch S k u w) atTop
      (𝓝 (∑ u, ch.P v u * hitDistLim ch S u w)) :=
    tendsto_finset_sum _ fun u _ => (hitDist_tendsto ch S u w).const_mul _
  refine tendsto_nhds_unique h1 ?_
  simpa [hitDist, hv] using h2

/-- Almost sure hitting of the skeleton holds under the uniform hitting estimate
of `WatchedChain` (which the descent hypothesis provides). -/
theorem tendsto_notHit_zero_of_uniform_hit {N : ℕ} {ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hhit : ∀ w, notHit ch S N w ≤ 1 - ε) (v : V) :
    Tendsto (fun k => notHit ch S k v) atTop (𝓝 0) := by
  have hM0 : (0:ℝ) ≤ 1 - ε := by linarith
  have hbound : ∀ j : ℕ, notHit ch S (j * N) v ≤ (1 - ε) ^ j :=
    fun j => notHit_mul_le ch S hM0 hhit j v
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => (0:ℝ))
    (h := fun k => (1 - ε) ^ (k / N)) tendsto_const_nhds ?_ ?_ ?_
  · have hpow : Tendsto (fun j : ℕ => (1 - ε) ^ j) atTop (𝓝 0) := by
      refine tendsto_pow_atTop_nhds_zero_of_lt_one hM0 ?_
      linarith
    have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
    have hdiv : Tendsto (fun k : ℕ => k / N) atTop atTop := by
      refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨b * N + N, fun a ha => ?_⟩
      exact (Nat.le_div_iff_mul_le hNpos).mpr (by omega)
    exact hpow.comp hdiv
  · exact fun k => notHit_nonneg ch S k v
  · intro k
    have hkN : (k / N) * N ≤ k := Nat.div_mul_le_self k N
    exact le_trans (notHit_antitone ch S hkN v) (hbound (k / N))

end Basic

section Trace

variable (ch : FinChain V) (S : Finset V)

/--
**The watched (traced) chain on the skeleton.**
`Q(v,w) = ∑_u P(v,u) · P_u(X_{σ_S} = w)`: one step of the original walk followed
by the excursion back to the skeleton.  This is a genuine transition kernel on
`S`, so all the estimates of `WatchedChain` apply to it verbatim.
-/
noncomputable def traceChain (hS : ∀ v, Tendsto (fun k => notHit ch S k v) atTop (𝓝 0)) :
    FinChain {x // x ∈ S} where
  P v w := ∑ u, ch.P v.1 u * hitDistLim ch S u w.1
  P_nonneg v w :=
    sum_nonneg fun u _ => mul_nonneg (ch.P_nonneg v.1 u) (hitDistLim_nonneg ch S u w.1)
  P_sum v := by
    have hswap : ∑ w : {x // x ∈ S}, ∑ u, ch.P v.1 u * hitDistLim ch S u w.1
        = ∑ u, ch.P v.1 u * ∑ w : {x // x ∈ S}, hitDistLim ch S u w.1 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum]
    have hfull : ∀ u : V, ∑ w : {x // x ∈ S}, hitDistLim ch S u w.1 = 1 := by
      intro u
      have h1 : ∑ w : {x // x ∈ S}, hitDistLim ch S u w.1
          = ∑ w ∈ S, hitDistLim ch S u w :=
        Finset.sum_coe_sort S fun w => hitDistLim ch S u w
      have h2 : ∑ w ∈ S, hitDistLim ch S u w = ∑ w, hitDistLim ch S u w := by
        refine Finset.sum_subset (Finset.subset_univ S) ?_
        intro w _ hw
        exact hitDistLim_eq_zero_of_not_mem ch S hw u
      rw [h1, h2, hitDistLim_sum ch S hS u]
    rw [hswap]
    simp only [hfull, mul_one]
    exact ch.P_sum v.1

end Trace

end IGS.Sec31
