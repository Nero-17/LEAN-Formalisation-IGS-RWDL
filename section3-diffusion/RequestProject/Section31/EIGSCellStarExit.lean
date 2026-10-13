import RequestProject.Section31.TraceDecomposition
import RequestProject.Section2StarExit
import RequestProject.Section31.EIGSDiscreteTraceGram

/-!
The first return to a skeleton need not be a jump to a distinct skeleton
vertex. This file keeps the existing return kernel unchanged and removes
its self loops explicitly. Both the departure distribution and the expected
accumulated excursion cost are obtained from the actual first-hitting
recursions, with the same factor `1 - P vertex vertex`.

This is an intermediate interface. The actual substituted-network
conductance identification and the uniform cell terminal bound still have
to be proved; neither is an assumption of a claimed final EIGS result here.
-/

namespace IGS.Sec31

open Finset Filter Topology

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

/-- The chain observed at the first subsequent distinct state. -/
noncomputable def distinctJumpChain (chain : FinChain Vertex)
    (departure_positive : ∀ vertex, 0 < 1 - chain.P vertex vertex) :
    FinChain Vertex where
  P vertex target :=
    (if vertex = target then 0 else chain.P vertex target) /
      (1 - chain.P vertex vertex)
  P_nonneg vertex target := div_nonneg
    (by split <;> first | exact le_rfl | exact chain.P_nonneg _ _)
    (departure_positive vertex).le
  P_sum vertex := by
    rw [← Finset.sum_div]
    have numerator :
        (∑ target, if vertex = target then (0 : ℝ) else chain.P vertex target) =
          1 - chain.P vertex vertex := by
      calc
        _ = ∑ target, (chain.P vertex target -
            if target = vertex then chain.P vertex vertex else 0) := by
          apply Finset.sum_congr rfl
          intro target _
          by_cases equal : target = vertex
          · subst target; simp
          · simp [equal, Ne.symm equal]
        _ = _ := by rw [Finset.sum_sub_distrib, chain.P_sum]; simp
    rw [numerator, div_self (departure_positive vertex).ne']

/-- The departure kernel is the existing chain's genuine first-hitting
distribution of the complement of the current state. -/
theorem distinctJumpChain_eq_first_hitting (chain : FinChain Vertex)
    (departure_positive : ∀ vertex, 0 < 1 - chain.P vertex vertex)
    (vertex target : Vertex) :
    (distinctJumpChain chain departure_positive).P vertex target =
      hitDistLim chain (Finset.univ.erase vertex) vertex target := by
  by_cases equal : vertex = target
  · subst target
    have unsupported := hitDistLim_eq_zero_of_not_mem chain
      (Finset.univ.erase vertex) (show vertex ∉ Finset.univ.erase vertex by simp) vertex
    simpa [distinctJumpChain] using unsupported.symm
  · have recurrence := hitDistLim_succ chain (Finset.univ.erase vertex)
      (show vertex ∉ Finset.univ.erase vertex by simp) target
    have split_sum :
        (∑ neighbour, chain.P vertex neighbour *
          hitDistLim chain (Finset.univ.erase vertex) neighbour target) =
        chain.P vertex vertex * hitDistLim chain (Finset.univ.erase vertex) vertex target +
          chain.P vertex target := by
      calc
        _ = ∑ neighbour,
            ((if neighbour = vertex then chain.P vertex vertex *
                hitDistLim chain (Finset.univ.erase vertex) vertex target else 0) +
              (if neighbour = target then chain.P vertex target else 0)) := by
          apply Finset.sum_congr rfl
          intro neighbour _
          by_cases origin : neighbour = vertex
          · subst neighbour
            simp [equal]
          · rw [hitDistLim_of_mem chain (Finset.univ.erase vertex)
              (show neighbour ∈ Finset.univ.erase vertex by simp [origin])]
            by_cases endpoint : neighbour = target
            · subst neighbour; simp [equal, origin]
            · simp [origin, endpoint]
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    rw [split_sum] at recurrence
    change (if vertex = target then 0 else chain.P vertex target) /
      (1 - chain.P vertex vertex) = _
    rw [if_neg equal]
    apply (div_eq_iff (departure_positive vertex).ne').mpr
    nlinarith

/-- A nonnegative supersolution bounds each actual truncated accumulated cost. -/
theorem cost_le_of_supersolution (chain : FinChain Vertex) (boundary : Finset Vertex)
    (duration value : Vertex → ℝ) (value_nonnegative : ∀ vertex, 0 ≤ value vertex)
    (supersolution : ∀ vertex ∉ boundary,
      duration vertex + ∑ target, chain.P vertex target * value target ≤ value vertex) :
    ∀ steps vertex, cost chain boundary duration steps vertex ≤ value vertex := by
  intro steps
  induction steps with
  | zero => intro vertex; exact value_nonnegative vertex
  | succ steps induction_hypothesis =>
      intro vertex
      by_cases on_boundary : vertex ∈ boundary
      · simpa only [cost, if_pos on_boundary] using value_nonnegative vertex
      · rw [cost_succ chain boundary on_boundary]
        apply le_trans _ (supersolution vertex on_boundary)
        exact add_le_add le_rfl (Finset.sum_le_sum fun target _ =>
          mul_le_mul_of_nonneg_left (induction_hypothesis target)
            (chain.P_nonneg vertex target))

/-- The bounded accumulated-cost limit obeys its exact first-step equation. -/
theorem costLim_first_step (chain : FinChain Vertex) (boundary : Finset Vertex)
    (duration : Vertex → ℝ) (duration_nonnegative : ∀ vertex, 0 ≤ duration vertex)
    {upper : ℝ} (bounded : ∀ steps vertex, cost chain boundary duration steps vertex ≤ upper)
    {vertex : Vertex} (outside : vertex ∉ boundary) :
    costLim chain boundary duration vertex = duration vertex +
      ∑ target, chain.P vertex target * costLim chain boundary duration target := by
  have shifted := (cost_tendsto chain boundary duration_nonnegative
    (fun steps => bounded steps vertex)).comp (tendsto_add_atTop_nat 1)
  have expanded : Tendsto
      (fun steps => duration vertex + ∑ target,
        chain.P vertex target * cost chain boundary duration steps target) atTop
      (𝓝 (duration vertex + ∑ target,
        chain.P vertex target * costLim chain boundary duration target)) := by
    exact Tendsto.const_add _ (tendsto_finset_sum _ fun target _ =>
      (cost_tendsto chain boundary duration_nonnegative
        (fun steps => bounded steps target)).const_mul _)
  exact tendsto_nhds_unique shifted
    (by simpa only [Function.comp_def, cost_succ chain boundary outside] using expanded)

/-- Repeated self returns consume precisely the same reciprocal-departure
factor as the first-distinct-state transition probabilities. -/
theorem costLim_until_distinct (chain : FinChain Vertex)
    (departure_positive : ∀ vertex, 0 < 1 - chain.P vertex vertex)
    (duration : Vertex → ℝ) (duration_nonnegative : ∀ vertex, 0 ≤ duration vertex)
    (vertex : Vertex) :
    costLim chain (Finset.univ.erase vertex) duration vertex =
      duration vertex / (1 - chain.P vertex vertex) := by
  let value : Vertex → ℝ := fun target =>
    if target = vertex then duration vertex / (1 - chain.P vertex vertex) else 0
  have value_nonnegative : ∀ target, 0 ≤ value target := by
    intro target
    dsimp [value]
    split
    · exact div_nonneg (duration_nonnegative vertex) (departure_positive vertex).le
    · exact le_rfl
  have supersolution : ∀ target ∉ Finset.univ.erase vertex,
      duration target + ∑ neighbour, chain.P target neighbour * value neighbour ≤
        value target := by
    intro target outside
    have equal : target = vertex := by simpa using outside
    subst target
    have cancellation : duration vertex / (1 - chain.P vertex vertex) *
        (1 - chain.P vertex vertex) = duration vertex :=
      div_mul_cancel₀ _ (departure_positive vertex).ne'
    simp only [value, if_pos rfl]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    nlinarith
  have bound : ∀ steps target,
      cost chain (Finset.univ.erase vertex) duration steps target ≤
        duration vertex / (1 - chain.P vertex vertex) := by
    intro steps target
    apply (cost_le_of_supersolution chain _ duration value value_nonnegative
      supersolution steps target).trans
    dsimp [value]
    split
    · exact le_rfl
    · exact div_nonneg (duration_nonnegative vertex) (departure_positive vertex).le
  have recurrence := costLim_first_step chain (Finset.univ.erase vertex) duration
    duration_nonnegative bound (show vertex ∉ Finset.univ.erase vertex by simp)
  have other_zero : ∀ target, target ≠ vertex →
      costLim chain (Finset.univ.erase vertex) duration target = 0 := by
    intro target different
    simp only [costLim, cost_of_mem chain (Finset.univ.erase vertex)
      (show target ∈ Finset.univ.erase vertex by simp [different]), ciSup_const]
  have sum_identity :
      (∑ target, chain.P vertex target *
        costLim chain (Finset.univ.erase vertex) duration target) =
      chain.P vertex vertex * costLim chain (Finset.univ.erase vertex) duration vertex := by
    apply Finset.sum_eq_single vertex
    · intro target _ different
      rw [other_zero target different, mul_zero]
    · simp
  rw [sum_identity]
    at recurrence
  apply (eq_div_iff (departure_positive vertex).ne').mpr
  nlinarith

/-- Removing the diagonal and dividing the reward by the departure
probability preserves the exact Poisson supersolution inequality. -/
theorem distinctJumpChain_supersolution_iff (chain : FinChain Vertex)
    (departure_positive : ∀ vertex, 0 < 1 - chain.P vertex vertex)
    (duration value : Vertex → ℝ) (vertex : Vertex) :
    (duration vertex / (1 - chain.P vertex vertex) +
        ∑ target, (distinctJumpChain chain departure_positive).P vertex target * value target ≤
      value vertex) ↔
    (duration vertex + ∑ target, chain.P vertex target * value target ≤ value vertex) := by
  have sum_identity : (1 - chain.P vertex vertex) *
      (∑ target, (distinctJumpChain chain departure_positive).P vertex target * value target) =
      (∑ target, chain.P vertex target * value target) -
        chain.P vertex vertex * value vertex := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ target, (chain.P vertex target * value target -
          if target = vertex then chain.P vertex vertex * value vertex else 0) := by
        apply Finset.sum_congr rfl
        intro target _
        by_cases equal : target = vertex
        · subst target; simp [distinctJumpChain]
        · simp only [distinctJumpChain, equal, Ne.symm equal, if_false, sub_zero]
          field_simp [(departure_positive vertex).ne']
      _ = _ := by rw [Finset.sum_sub_distrib]; simp
  have cancellation : (1 - chain.P vertex vertex) *
      (duration vertex / (1 - chain.P vertex vertex)) = duration vertex :=
    mul_div_cancel₀ _ (departure_positive vertex).ne'
  constructor
  · intro accelerated
    have multiplied := mul_le_mul_of_nonneg_left accelerated (departure_positive vertex).le
    rw [mul_add, cancellation, sum_identity] at multiplied
    nlinarith
  · intro original
    apply (mul_le_mul_iff_right₀ (departure_positive vertex)).mp
    rw [mul_add, cancellation, sum_identity]
    nlinarith

/-- The full expected accumulated cost up to any target set is unchanged
when self returns are erased and each state's excursion duration is divided
by its departure probability. Boundedness here concerns the constructed
accelerated chain; the actual EIGS bound is a later consumer. -/
theorem costLim_distinctJumpChain (chain : FinChain Vertex)
    (departure_positive : ∀ vertex, 0 < 1 - chain.P vertex vertex)
    (boundary : Finset Vertex) (duration : Vertex → ℝ)
    (duration_nonnegative : ∀ vertex, 0 ≤ duration vertex)
    {upper : ℝ}
    (accelerated_bound : ∀ steps vertex,
      cost (distinctJumpChain chain departure_positive) boundary
        (fun target => duration target / (1 - chain.P target target)) steps vertex ≤ upper)
    (vertex : Vertex) :
    costLim chain boundary duration vertex =
      costLim (distinctJumpChain chain departure_positive) boundary
        (fun target => duration target / (1 - chain.P target target)) vertex := by
  let accelerated_duration := fun target => duration target / (1 - chain.P target target)
  let accelerated_value := costLim (distinctJumpChain chain departure_positive)
    boundary accelerated_duration
  have accelerated_nonnegative : ∀ target, 0 ≤ accelerated_duration target :=
    fun target => div_nonneg (duration_nonnegative target) (departure_positive target).le
  have accelerated_value_nonnegative : ∀ target, 0 ≤ accelerated_value target :=
    fun target => costLim_nonneg _ _ accelerated_nonnegative
      (fun steps => accelerated_bound steps target)
  have accelerated_value_bound : ∀ target, accelerated_value target ≤ upper :=
    fun target => ciSup_le (fun steps => accelerated_bound steps target)
  have original_super : ∀ target ∉ boundary,
      duration target + ∑ neighbour, chain.P target neighbour * accelerated_value neighbour ≤
        accelerated_value target := by
    intro target outside
    apply (distinctJumpChain_supersolution_iff chain departure_positive duration
      accelerated_value target).mp
    exact costLim_supersolution _ _ accelerated_nonnegative accelerated_bound outside
  have original_bound : ∀ steps target, cost chain boundary duration steps target ≤ upper := by
    intro steps target
    exact (cost_le_of_supersolution chain boundary duration accelerated_value
      accelerated_value_nonnegative original_super steps target).trans
        (accelerated_value_bound target)
  apply le_antisymm
  · exact ciSup_le fun steps => cost_le_of_supersolution chain boundary duration
      accelerated_value accelerated_value_nonnegative original_super steps vertex
  · have original_nonnegative : ∀ target, 0 ≤ costLim chain boundary duration target :=
      fun target => costLim_nonneg chain boundary duration_nonnegative
        (fun steps => original_bound steps target)
    have accelerated_super : ∀ target ∉ boundary,
        accelerated_duration target + ∑ neighbour,
          (distinctJumpChain chain departure_positive).P target neighbour *
            costLim chain boundary duration neighbour ≤ costLim chain boundary duration target := by
      intro target outside
      apply (distinctJumpChain_supersolution_iff chain departure_positive duration
        (costLim chain boundary duration) target).mpr
      exact costLim_supersolution chain boundary duration_nonnegative original_bound outside
    exact ciSup_le fun steps => cost_le_of_supersolution
      (distinctJumpChain chain departure_positive) boundary accelerated_duration
      (costLim chain boundary duration) original_nonnegative accelerated_super steps vertex

/-- The smallest example distinguishing return observation from distinct
skeleton jumps: the simple walk on the two-edge path. -/
noncomputable def twoEdgePathChain : FinChain (Fin 3) where
  P vertex target := if vertex.val = 1 then (if target.val = 1 then 0 else 1 / 2)
    else (if target.val = 1 then 1 else 0)
  P_nonneg vertex target := by split <;> split <;> norm_num
  P_sum vertex := by fin_cases vertex <;> norm_num [Fin.sum_univ_succ] <;> decide

def twoEdgePathSkeleton : Finset (Fin 3) :=
  Finset.univ.filter (fun vertex => vertex.val ≠ 1)

theorem twoEdgePath_hits_skeleton (vertex : Fin 3) :
    Tendsto (fun steps => notHit twoEdgePathChain twoEdgePathSkeleton steps vertex)
      atTop (𝓝 0) := by
  apply tendsto_notHit_zero_of_uniform_hit twoEdgePathChain twoEdgePathSkeleton
    (N := 1) (ε := 1) (by norm_num) (by norm_num) (by norm_num) _ vertex
  intro start
  fin_cases start <;> norm_num [notHit, twoEdgePathChain, twoEdgePathSkeleton, Fin.sum_univ_succ]

theorem twoEdgePath_return_diagonal :
    (traceChain twoEdgePathChain twoEdgePathSkeleton twoEdgePath_hits_skeleton).P
      ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 / 2 := by
  have left := hitDistLim_of_mem twoEdgePathChain twoEdgePathSkeleton
    (show (0 : Fin 3) ∈ twoEdgePathSkeleton by decide) 0
  have right := hitDistLim_of_mem twoEdgePathChain twoEdgePathSkeleton
    (show (2 : Fin 3) ∈ twoEdgePathSkeleton by decide) 0
  have middle := hitDistLim_succ twoEdgePathChain twoEdgePathSkeleton
    (show (1 : Fin 3) ∉ twoEdgePathSkeleton by decide) 0
  simp +decide at left right
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] at middle
  change hitDistLim twoEdgePathChain twoEdgePathSkeleton 1 0 =
    1 / 2 * hitDistLim twoEdgePathChain twoEdgePathSkeleton 0 0 +
      (0 * hitDistLim twoEdgePathChain twoEdgePathSkeleton 1 0 +
        (1 / 2 * hitDistLim twoEdgePathChain twoEdgePathSkeleton 2 0 + 0)) at middle
  rw [left, right] at middle
  norm_num at middle
  change (∑ neighbour : Fin 3, twoEdgePathChain.P 0 neighbour *
    hitDistLim twoEdgePathChain twoEdgePathSkeleton neighbour 0) = 1 / 2
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  change (0 * hitDistLim twoEdgePathChain twoEdgePathSkeleton 0 0 +
    (1 * hitDistLim twoEdgePathChain twoEdgePathSkeleton 1 0 +
      (0 * hitDistLim twoEdgePathChain twoEdgePathSkeleton 2 0 + 0))) = 1 / 2
  rw [middle]
  ring

end IGS.Sec31

namespace EIGS

open scoped BigOperators Classical
open Matrix

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]

/-- The actual simple random walk viewed in the finite-chain interface. -/
noncomputable def graphWalkChain (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degree_positive : ∀ vertex, 0 < graph.degree vertex) : IGS.Sec31.FinChain Vertex where
  P := transProb graph
  P_nonneg := transProb_nonneg
  P_sum vertex := transProb_sum (degree_positive vertex)

theorem graphWalkChain_notHit (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degree_positive : ∀ vertex, 0 < graph.degree vertex) (boundary : Finset Vertex) :
    ∀ steps vertex,
      IGS.Sec31.notHit (graphWalkChain graph degree_positive) boundary steps vertex =
        surv graph boundaryᶜ steps vertex := by
  intro steps
  induction steps with
  | zero => intro vertex; by_cases inside : vertex ∈ boundary <;>
      simp [IGS.Sec31.notHit, surv, inside]
  | succ steps induction_hypothesis =>
      intro vertex
      by_cases inside : vertex ∈ boundary
      · simp [IGS.Sec31.notHit, surv, inside]
      · simp only [IGS.Sec31.notHit, inside, if_false, surv,
          Finset.mem_compl, not_false_eq_true, if_true, graphWalkChain]
        exact Finset.sum_congr rfl fun target _ =>
          congrArg (fun value => transProb graph vertex target * value)
            (induction_hypothesis target)

/-- The two independently defined means, a supremum of truncated hitting
costs and the genuine survival series, agree on the actual graph walk. -/
theorem graphWalkChain_hitTime (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (connected : graph.Connected) (degree_positive : ∀ vertex, 0 < graph.degree vertex)
    (boundary : Finset Vertex) (boundary_nonempty : boundary.Nonempty) (vertex : Vertex) :
    IGS.Sec31.hitTime (graphWalkChain graph degree_positive) boundary vertex =
      expExit graph boundaryᶜ vertex := by
  have proper : (boundaryᶜ)ᶜ.Nonempty := by simpa using boundary_nonempty
  have bounded : ∀ steps,
      IGS.Sec31.partialHit (graphWalkChain graph degree_positive) boundary steps vertex ≤
        expExit graph boundaryᶜ vertex := by
    intro steps
    simp only [IGS.Sec31.partialHit, graphWalkChain_notHit]
    exact (expExit_summable connected proper vertex).sum_le_tsum _
      (fun _ _ => surv_nonneg _ _)
  have first_limit := IGS.Sec31.partialHit_tendsto
    (graphWalkChain graph degree_positive) boundary bounded
  have second_limit := (expExit_summable connected proper vertex).hasSum.tendsto_sum_nat
  apply tendsto_nhds_unique first_limit
  simpa only [IGS.Sec31.partialHit, graphWalkChain_notHit, expExit] using second_limit

/-- The genuine first-hitting probabilities are harmonic before hitting. -/
theorem graphWalkChain_first_hitting_harmonic (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (degree_positive : ∀ vertex, 0 < graph.degree vertex)
    (boundary : Finset Vertex) (target : Vertex) {vertex : Vertex}
    (outside : vertex ∉ boundary) :
    (graph.lapMatrix ℝ *ᵥ
      (fun start => IGS.Sec31.hitDistLim (graphWalkChain graph degree_positive)
        boundary start target)) vertex = 0 := by
  have recurrence := IGS.Sec31.hitDistLim_succ (graphWalkChain graph degree_positive)
    boundary outside target
  have averaged := transProb_smul_sum (degree_positive vertex)
    (fun start => IGS.Sec31.hitDistLim (graphWalkChain graph degree_positive)
      boundary start target)
  change IGS.Sec31.hitDistLim (graphWalkChain graph degree_positive) boundary vertex target =
    ∑ start, transProb graph vertex start * _ at recurrence
  rw [averaged] at recurrence
  have multiplied : (graph.degree vertex : ℝ) *
      IGS.Sec31.hitDistLim (graphWalkChain graph degree_positive) boundary vertex target =
      ∑ start ∈ graph.neighborFinset vertex,
        IGS.Sec31.hitDistLim (graphWalkChain graph degree_positive) boundary start target := by
    rw [recurrence]
    exact mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr (degree_positive vertex).ne') _
  rw [lapMatrix_mulVec_apply, multiplied, sub_self]

/-- First-hitting probabilities equal the unique harmonic function with
their actual indicator boundary values. -/
theorem graphWalkChain_first_hitting_eq_profile (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (connected : graph.Connected)
    (degree_positive : ∀ vertex, 0 < graph.degree vertex)
    (boundary : Finset Vertex) (boundary_nonempty : boundary.Nonempty)
    (target : Vertex) (profile : Vertex → ℝ)
    (profile_boundary : ∀ vertex ∈ boundary, profile vertex = if vertex = target then 1 else 0)
    (profile_harmonic : ∀ vertex, vertex ∉ boundary →
      (graph.lapMatrix ℝ *ᵥ profile) vertex = 0) (vertex : Vertex) :
    IGS.Sec31.hitDistLim (graphWalkChain graph degree_positive) boundary vertex target =
      profile vertex := by
  have proper : (boundaryᶜ)ᶜ.Nonempty := by simpa using boundary_nonempty
  let hitting := fun start =>
    IGS.Sec31.hitDistLim (graphWalkChain graph degree_positive) boundary start target
  have same_boundary : ∀ start, start ∉ boundaryᶜ → hitting start = profile start := by
    intro start outside
    have inside : start ∈ boundary := by simpa using outside
    exact (IGS.Sec31.hitDistLim_of_mem (graphWalkChain graph degree_positive)
      boundary inside target).trans (profile_boundary start inside).symm
  have first := subharmonic_nonpos (G := graph) connected proper
    (f := hitting - profile)
    (fun start outside => by simp only [Pi.sub_apply, same_boundary start outside, sub_self, le_refl])
    (fun start inside => by
      have outside : start ∉ boundary := Finset.mem_compl.mp inside
      rw [Matrix.mulVec_sub]
      simp only [Pi.sub_apply]
      rw [graphWalkChain_first_hitting_harmonic graph degree_positive boundary target outside,
        profile_harmonic start outside]
      simp)
  have second := subharmonic_nonpos (G := graph) connected proper
    (f := profile - hitting)
    (fun start outside => by simp only [Pi.sub_apply, same_boundary start outside, sub_self, le_refl])
    (fun start inside => by
      have outside : start ∉ boundary := Finset.mem_compl.mp inside
      rw [Matrix.mulVec_sub]
      simp only [Pi.sub_apply]
      rw [profile_harmonic start outside,
        graphWalkChain_first_hitting_harmonic graph degree_positive boundary target outside]
      simp)
  exact le_antisymm (sub_nonpos.mp (first vertex)) (sub_nonpos.mp (second vertex))

namespace Network

open IGS.Sec31

/-- The actual oriented-edge energy pairing equals the simple graph
Laplacian pairing for unit edge resistances. -/
theorem unit_energyInner_laplacian {K : ℕ} (network : Network K)
    (loopless : network.Loopless) (unique_edges : network.EdgesUnique)
    (first second : network.V → ℝ) :
    (network.potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energyInner first second =
      ∑ vertex, second vertex * (network.toSimpleGraph.lapMatrix ℝ *ᵥ first) vertex := by
  have divergence : ∀ vertex,
      network.div (fun edge => first (network.tail edge) - first (network.head edge)) vertex =
        (network.toSimpleGraph.lapMatrix ℝ *ᵥ first) vertex := by
    intro vertex
    rw [network.div_restrict_eq_simpleGraph loopless unique_edges
      (fun source sink => first source - first sink) (by intro source sink; ring)]
    change flowDiv network.toSimpleGraph (fun source sink => first source - first sink) vertex = _
    rw [flowDiv_gradient]
  have green := network.sum_potential_mul_div
    (fun edge => first (network.tail edge) - first (network.head edge)) second
  simp only [divergence] at green
  simpa only [FiniteNetwork.energyInner, potentialNetwork, inv_one, one_mul] using green.symm

/-- Harmonicity of an actual unit-energy minimizer, derived by testing with
one-vertex zero-boundary perturbations. -/
theorem unit_minimum_harmonic {K : ℕ} (network : Network K)
    (loopless : network.Loopless) (unique_edges : network.EdgesUnique)
    (boundary : Finset network.V) (potential : network.V → ℝ)
    (minimum : ∀ competitor : network.V → ℝ,
      (∀ vertex ∈ boundary, competitor vertex = potential vertex) →
      (network.potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy potential ≤
        (network.potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy competitor)
    (vertex : network.V) (outside : vertex ∉ boundary) :
    (network.toSimpleGraph.lapMatrix ℝ *ᵥ potential) vertex = 0 := by
  have orthogonal := (network.potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energyInner_eq_zero_of_min
    (↑boundary : Set network.V) potential potential (fun _ _ => rfl) minimum
    (fun target => if target = vertex then 1 else 0) (by
      intro target inside
      have different : target ≠ vertex := by
        intro equal
        subst target
        exact outside inside
      exact if_neg different)
  rw [network.unit_energyInner_laplacian loopless unique_edges] at orthogonal
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using orthogonal

end Network

/-- The simple random walk on the actual original-unit Xi graph. -/
noncomputable def xiGraphWalkChain {K : ℕ} (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ) :
    IGS.Sec31.FinChain (XiVtx system level) :=
  graphWalkChain (XiSimpleGraph system level) (fun vertex => by
    exact_mod_cast xiSimpleGraph_degree_positive system rule_connected level vertex)

/-- The true first-hitting distribution of the actual coarse skeleton is
the already-constructed unit-resistance trace extension, at every depth. -/
theorem xiGraphWalkChain_first_hitting_eq_trace {K : ℕ} (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (target : XiVtx system coarse)
    (vertex : XiVtx system (coarse + steps)) :
    IGS.Sec31.hitDistLim (xiGraphWalkChain system rule_connected (coarse + steps))
        (Finset.univ.image (xiForward system coarse steps)) vertex
        (xiForward system coarse steps target) =
      xiUnitTraceExtension system rule_connected coarse steps
        (fun old_vertex => if old_vertex = target then 1 else 0) vertex := by
  apply graphWalkChain_first_hitting_eq_profile (XiSimpleGraph system (coarse + steps))
    (xiSimpleGraph_connected system rule_connected _) _
    (Finset.univ.image (xiForward system coarse steps))
    (Finset.image_nonempty.mpr ⟨target, Finset.mem_univ _⟩)
  · intro boundary_vertex membership
    obtain ⟨old_vertex, _, rfl⟩ := Finset.mem_image.mp membership
    rw [xiUnitTraceExtension_boundary]
    by_cases equal : old_vertex = target
    · simp [equal]
    · simp [equal, (xiForward_injective system coarse steps).ne equal]
  · intro inside_vertex outside
    apply (XiNetwork system (coarse + steps)).unit_minimum_harmonic
      (xiNetwork_loopless system rule_connected rules_loopless _)
      (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent _)
      (Finset.univ.image (xiForward system coarse steps)) _ _ inside_vertex outside
    intro competitor competitor_boundary
    apply xiUnitTraceExtension_minimal system rule_connected coarse steps _ competitor
    intro old_vertex
    exact (competitor_boundary (xiForward system coarse steps old_vertex)
      (Finset.mem_image.mpr ⟨old_vertex, Finset.mem_univ _, rfl⟩)).trans
        (xiUnitTraceExtension_boundary system rule_connected coarse steps _ old_vertex)

/-- An exact Dirichlet comparison for reaching an intermediate boundary.
The comparison uses actual survival-series means and the finite maximum
principle, without assuming a strong Markov identity. -/
theorem expExit_le_inner_add_boundary_upper (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (connected : graph.Connected)
    {inner outer : Finset Vertex} (contained : inner ⊆ outer)
    (proper : outerᶜ.Nonempty) (upper : ℝ)
    (boundary_upper : ∀ vertex, vertex ∉ inner → expExit graph outer vertex ≤ upper)
    (vertex : Vertex) :
    expExit graph outer vertex ≤ expExit graph inner vertex + upper := by
  have inner_proper : innerᶜ.Nonempty := by
    obtain ⟨outside, membership⟩ := proper
    refine ⟨outside, Finset.mem_compl.mpr ?_⟩
    exact fun inside => (Finset.mem_compl.mp membership) (contained inside)
  have outer_system := exitSystem_expExit connected proper
  have inner_system := exitSystem_expExit connected inner_proper
  have comparison := subharmonic_nonpos (G := graph) connected inner_proper
    (f := fun target => expExit graph outer target - expExit graph inner target - upper)
    (fun target outside => by
      dsimp only
      rw [expExit_zero_of_notMem outside]
      linarith [boundary_upper target outside])
    (fun target inside => by
      have constant_zero : (graph.lapMatrix ℝ *ᵥ (fun _ : Vertex => upper)) target = 0 := by
        rw [lapMatrix_mulVec_apply]
        simp
      change ((graph.lapMatrix ℝ *ᵥ
        ((expExit graph outer - expExit graph inner) - fun _ : Vertex => upper))) target ≤ 0
      rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
      simp only [Pi.sub_apply]
      rw [outer_system.2 target (contained inside), inner_system.2 target inside, constant_zero]
      simp)
  linarith [comparison vertex]

/-- Every starting point in a fixed domain is controlled by the time to
reach its center or exterior, plus the actual center exit mean. -/
theorem expExit_le_erased_center_add_center (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (connected : graph.Connected)
    (domain : Finset Vertex) (proper : domainᶜ.Nonempty)
    (center vertex : Vertex) :
    expExit graph domain vertex ≤ expExit graph (domain.erase center) vertex +
      expExit graph domain center := by
  apply expExit_le_inner_add_boundary_upper graph connected (Finset.erase_subset _ _) proper
  intro target outside
  by_cases equal : target = center
  · subst target; exact le_rfl
  · have target_outside : target ∉ domain := by
      intro inside
      exact outside (Finset.mem_erase.mpr ⟨equal, inside⟩)
    rw [expExit_zero_of_notMem target_outside]
    exact expExit_nonneg center

/-- The preceding comparison on the actual multistep incident star. Its
remaining first term is actual hitting of the center or a far cell terminal,
not an assumed uniform exit bound. -/
theorem xiIncidentStarDomain_expExit_le_erased_add_center {K : ℕ}
    (system : EIGSData K) (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) (center : XiVtx system coarse)
    (vertex : XiVtx system (coarse + steps)) :
    expExit (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center) vertex ≤
      expExit (XiSimpleGraph system (coarse + steps))
        ((xiIncidentStarDomain system coarse steps center).erase
          (xiForward system coarse steps center)) vertex +
      expExit (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center) (xiForward system coarse steps center) :=
  expExit_le_erased_center_add_center _ (xiSimpleGraph_connected system rule_connected _)
    _ (xiIncidentStarDomain_complement_nonempty system coarse steps center) _ _

end EIGS

#print axioms IGS.Sec31.distinctJumpChain_eq_first_hitting
#print axioms IGS.Sec31.cost_le_of_supersolution
#print axioms IGS.Sec31.costLim_first_step
#print axioms IGS.Sec31.costLim_until_distinct
#print axioms IGS.Sec31.distinctJumpChain_supersolution_iff
#print axioms IGS.Sec31.costLim_distinctJumpChain
#print axioms IGS.Sec31.twoEdgePath_return_diagonal
#print axioms EIGS.graphWalkChain_notHit
#print axioms EIGS.graphWalkChain_hitTime
#print axioms EIGS.graphWalkChain_first_hitting_harmonic
#print axioms EIGS.graphWalkChain_first_hitting_eq_profile
#print axioms EIGS.Network.unit_energyInner_laplacian
#print axioms EIGS.Network.unit_minimum_harmonic
#print axioms EIGS.xiGraphWalkChain_first_hitting_eq_trace
#print axioms EIGS.expExit_le_inner_add_boundary_upper
#print axioms EIGS.expExit_le_erased_center_add_center
#print axioms EIGS.xiIncidentStarDomain_expExit_le_erased_add_center
