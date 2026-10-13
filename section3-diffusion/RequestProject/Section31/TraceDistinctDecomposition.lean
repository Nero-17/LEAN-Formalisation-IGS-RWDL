import RequestProject.Section31.EIGSCellStarExit

namespace IGS.Sec31
open Finset Filter Topology
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exit_time_le_skeleton_add_accumulated_cost
    (ch : FinChain V) (S B : Finset V)
    (hS : ∀ v, Tendsto (fun k => notHit ch S k v) atTop (𝓝 0))
    {RS : ℝ} (hRS : ∀ (K : ℕ) (v : V), partialHit ch S K v ≤ RS)
    {upper : ℝ} (upper_nonnegative : 0 ≤ upper)
    (accumulated_bound : ∀ steps (vertex : {x // x ∈ S}),
      cost (traceChain ch S hS) (termIn S B) (excursionTime ch S) steps vertex ≤ upper)
    (z : V) :
    hitTime ch B z ≤ RS + upper := by
  classical
  set Q := traceChain ch S hS with hQdef
  set B' := termIn S B with hB'
  set d' := excursionTime ch S with hd'
  have hQP : ∀ (v' y : {x // x ∈ S}),
      Q.P v' y = ∑ u, ch.P (v' : V) u * hitDistLim ch S u (y : V) := fun _ _ => rfl
  -- the accumulated jump time of the watched chain, extended by `0` off the skeleton
  set h : V → ℝ := fun v => if hv : v ∈ S then costLim Q B' d' ⟨v, hv⟩ else 0 with hh
  have hitTimeS_nonneg : ∀ v, 0 ≤ hitTime ch S v := fun v =>
    hitTime_nonneg ch S (fun K => hRS K v)
  have hd'0 : ∀ w : {x // x ∈ S}, 0 ≤ d' w := by
    intro w
    have hsum : 0 ≤ ∑ u, ch.P (w : V) u * hitTime ch S u :=
      sum_nonneg fun u _ => mul_nonneg (ch.P_nonneg _ u) (hitTimeS_nonneg u)
    simp only [hd', excursionTime]
    linarith
  have hcost : ∀ steps vertex, cost Q B' d' steps vertex ≤ upper := accumulated_bound
  have hDCR : 0 ≤ upper := upper_nonnegative
  have hh0 : ∀ v, 0 ≤ h v := by
    intro v
    simp only [hh]
    split
    · exact costLim_nonneg Q B' hd'0 (fun k => hcost k _)
    · exact le_rfl
  have hhle : ∀ v, h v ≤ upper := by
    intro v
    simp only [hh]
    split
    · exact ciSup_le fun steps => hcost steps _
    · exact hDCR
  have hh_mem : ∀ w : {x // x ∈ S}, h (w : V) = costLim Q B' d' w := by
    intro w
    simp only [hh, dif_pos w.2]
  have hh_not_mem : ∀ {w : V}, w ∉ S → h w = 0 := by
    intro w hw
    simp only [hh, dif_neg hw]
  -- restricting a sum over the state space to the skeleton
  have hrestrict : ∀ u : V, ∑ y : {x // x ∈ S}, hitDistLim ch S u (y : V) * h (y : V)
      = ∑ w, hitDistLim ch S u w * h w := by
    intro u
    have h1 : ∑ y : {x // x ∈ S}, hitDistLim ch S u (y : V) * h (y : V)
        = ∑ w ∈ S, hitDistLim ch S u w * h w :=
      Finset.sum_coe_sort S fun w => hitDistLim ch S u w * h w
    rw [h1]
    refine Finset.sum_subset (Finset.subset_univ S) ?_
    intro w _ hw
    rw [hh_not_mem hw]; ring
  -- the candidate supersolution
  set g : V → ℝ := fun v => hitTime ch S v + ∑ w, hitDistLim ch S v w * h w with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v =>
    add_nonneg (hitTimeS_nonneg v)
      (sum_nonneg fun w _ => mul_nonneg (hitDistLim_nonneg ch S v w) (hh0 w))
  have hswap : ∀ v ∉ S, ∑ w, hitDistLim ch S v w * h w
      = ∑ u, ch.P v u * ∑ w, hitDistLim ch S u w * h w := by
    intro v hv
    calc ∑ w, hitDistLim ch S v w * h w
        = ∑ w, (∑ u, ch.P v u * hitDistLim ch S u w) * h w := by
          exact sum_congr rfl fun w _ => by rw [hitDistLim_succ ch S hv w]
      _ = ∑ w, ∑ u, ch.P v u * (hitDistLim ch S u w * h w) := by
          refine sum_congr rfl fun w _ => ?_
          rw [Finset.sum_mul]
          exact sum_congr rfl fun u _ => by ring
      _ = ∑ u, ∑ w, ch.P v u * (hitDistLim ch S u w * h w) := Finset.sum_comm
      _ = ∑ u, ch.P v u * ∑ w, hitDistLim ch S u w * h w :=
          sum_congr rfl fun u _ => by rw [Finset.mul_sum]
  have hsuper : ∀ v ∉ B, 1 + ∑ u, ch.P v u * g u ≤ g v := by
    intro v hvB
    by_cases hv : v ∈ S
    · -- a skeleton point: this is the supersolution property of the watched chain
      set v' : {x // x ∈ S} := ⟨v, hv⟩ with hv'
      have hv'B : v' ∉ B' := by simp [hB', hv', hvB]
      have hgv : g v = h v := by
        have hdirac : ∑ w, hitDistLim ch S v w * h w = h v := by
          simp [hitDistLim_of_mem ch S hv]
        simp only [hg, hitTime_of_mem ch S hv, hdirac, zero_add]
      have hgu : ∑ u, ch.P v u * g u
          = (∑ u, ch.P v u * hitTime ch S u)
            + ∑ u, ch.P v u * ∑ w, hitDistLim ch S u w * h w := by
        rw [← Finset.sum_add_distrib]
        exact sum_congr rfl fun u _ => by simp only [hg]; ring
      have hQsum : ∑ y : {x // x ∈ S}, Q.P v' y * costLim Q B' d' y
          = ∑ u, ch.P v u * ∑ w, hitDistLim ch S u w * h w := by
        calc ∑ y : {x // x ∈ S}, Q.P v' y * costLim Q B' d' y
            = ∑ y : {x // x ∈ S},
                (∑ u, ch.P v u * hitDistLim ch S u (y : V)) * h (y : V) := by
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [hQP v' y, hh_mem y]
          _ = ∑ y : {x // x ∈ S}, ∑ u,
                ch.P v u * (hitDistLim ch S u (y : V) * h (y : V)) := by
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [Finset.sum_mul]
              exact sum_congr rfl fun u _ => by ring
          _ = ∑ u, ∑ y : {x // x ∈ S},
                ch.P v u * (hitDistLim ch S u (y : V) * h (y : V)) := Finset.sum_comm
          _ = ∑ u, ch.P v u * ∑ w, hitDistLim ch S u w * h w := by
              refine sum_congr rfl fun u _ => ?_
              rw [← Finset.mul_sum, hrestrict u]
      have hsuperQ := costLim_supersolution Q B' hd'0 hcost hv'B
      rw [hQsum] at hsuperQ
      have hd'v : d' v' = 1 + ∑ u, ch.P v u * hitTime ch S u := rfl
      rw [hgv, hh_mem v', hgu]
      rw [hd'v] at hsuperQ
      linarith
    · -- off the skeleton: the first-step recursion, with equality
      have h1 : hitTime ch S v = 1 + ∑ u, ch.P v u * hitTime ch S u :=
        hitTime_succ ch S (fun K u => hRS K u) hv
      have h2 : ∑ u, ch.P v u * g u
          = (∑ u, ch.P v u * hitTime ch S u)
            + ∑ u, ch.P v u * ∑ w, hitDistLim ch S u w * h w := by
        rw [← Finset.sum_add_distrib]
        exact sum_congr rfl fun u _ => by simp only [hg]; ring
      have h3 := hswap v hv
      simp only [hg]
      rw [h1, h2, h3]
      linarith
  -- conclusion
  have hmain : hitTime ch B z ≤ g z := hitTime_le_of_supersolution ch B hg0 hsuper z
  have hgz : g z ≤ RS + upper := by
    have hA : hitTime ch S z ≤ RS := ciSup_le fun K => hRS K z
    have hB2 : ∑ w, hitDistLim ch S z w * h w ≤ upper := by
      calc ∑ w, hitDistLim ch S z w * h w
          ≤ ∑ w, hitDistLim ch S z w * (upper) :=
            sum_le_sum fun w _ =>
              mul_le_mul_of_nonneg_left (hhle w) (hitDistLim_nonneg ch S z w)
        _ = (∑ w, hitDistLim ch S z w) * (upper) := by rw [Finset.sum_mul]
        _ ≤ 1 * (upper) := mul_le_mul_of_nonneg_right (hitDistLim_sum_le_one ch S z) hDCR
        _ = upper := one_mul _
    simp only [hg]
    linarith
  linarith


/-- Excursion decomposition after erasing self returns. Only the distinct
jump count and the duration divided by departure probability are bounded.
This bridge does not assert that any particular graph satisfies those bounds. -/
theorem exit_time_le_distinct_skeleton_add_cost
    (chain : FinChain V) (skeleton boundary : Finset V)
    (hits : ∀ vertex, Tendsto (fun steps => notHit chain skeleton steps vertex) atTop (𝓝 0))
    {reach_bound : ℝ}
    (reach : ∀ steps vertex, partialHit chain skeleton steps vertex ≤ reach_bound)
    (departure : ∀ vertex, 0 < 1 - (traceChain chain skeleton hits).P vertex vertex)
    {duration_bound jump_bound : ℝ}
    (duration_nonnegative : 0 ≤ duration_bound) (jumps_nonnegative : 0 ≤ jump_bound)
    (duration : ∀ vertex,
      excursionTime chain skeleton vertex /
        (1 - (traceChain chain skeleton hits).P vertex vertex) ≤ duration_bound)
    (jumps : ∀ steps vertex,
      partialHit (distinctJumpChain (traceChain chain skeleton hits) departure)
        (termIn skeleton boundary) steps vertex ≤ jump_bound)
    (vertex : V) :
    hitTime chain boundary vertex ≤ reach_bound + duration_bound * jump_bound := by
  have excursion_nonnegative : ∀ target, 0 ≤ excursionTime chain skeleton target := by
    intro target
    apply add_nonneg zero_le_one
    exact sum_nonneg fun other _ => mul_nonneg (chain.P_nonneg _ _)
      (hitTime_nonneg chain skeleton (fun steps => reach steps other))
  have accelerated_nonnegative : ∀ target,
      0 ≤ excursionTime chain skeleton target /
        (1 - (traceChain chain skeleton hits).P target target) :=
    fun target => div_nonneg (excursion_nonnegative target) (departure target).le
  have accelerated_bound : ∀ steps target,
      cost (distinctJumpChain (traceChain chain skeleton hits) departure)
        (termIn skeleton boundary)
        (fun target => excursionTime chain skeleton target /
          (1 - (traceChain chain skeleton hits).P target target)) steps target ≤
        duration_bound * jump_bound := by
    intro steps target
    exact (cost_le_mul_partialHit _ _ duration_nonnegative duration steps target).trans
      (mul_le_mul_of_nonneg_left (jumps steps target) duration_nonnegative)
  have accelerated_value_nonnegative : ∀ target,
      0 ≤ costLim (distinctJumpChain (traceChain chain skeleton hits) departure)
        (termIn skeleton boundary)
        (fun target => excursionTime chain skeleton target /
          (1 - (traceChain chain skeleton hits).P target target)) target :=
    fun target => costLim_nonneg _ _ accelerated_nonnegative
      (fun steps => accelerated_bound steps target)
  apply exit_time_le_skeleton_add_accumulated_cost chain skeleton boundary hits reach
    (mul_nonneg duration_nonnegative jumps_nonnegative) _ vertex
  intro steps target
  apply (cost_le_of_supersolution (traceChain chain skeleton hits)
    (termIn skeleton boundary) (excursionTime chain skeleton) _
    accelerated_value_nonnegative ?_ steps target).trans
  · exact ciSup_le fun count => accelerated_bound count target
  · intro start outside
    apply (distinctJumpChain_supersolution_iff (traceChain chain skeleton hits) departure
      (excursionTime chain skeleton) _ start).mp
    exact costLim_supersolution _ _ accelerated_nonnegative accelerated_bound outside

end IGS.Sec31

#print axioms IGS.Sec31.exit_time_le_skeleton_add_accumulated_cost
#print axioms IGS.Sec31.exit_time_le_distinct_skeleton_add_cost
