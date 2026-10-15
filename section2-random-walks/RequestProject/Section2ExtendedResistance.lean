import RequestProject.Section2Cuts
import Mathlib.Data.ENNReal.Operations

/-! Extended effective resistance for every pair in an arbitrary finite network.
Distinct-terminal resistance is the ENNReal infimum of actual unit-flow energies.
The graph-reachability equivalence is proved from Kirchhoff's cut identity;
infinity is therefore a consequence of absence of an electrical transport flow.
Coincident terminals are assigned zero, as required by the diagonal convention.
No connectedness of the whole graph or strict positivity of edge weights is used. -/

namespace EIGS.Network

open scoped BigOperators Classical ENNReal

variable {K : ℕ} (network : EIGS.Network K)

theorem flow_nonempty_of_reachable (source sink : network.V)
    (distinct : source ≠ sink) (reachable : network.toSimpleGraph.Reachable source sink) :
    Nonempty (network.Flow source sink) := by
  obtain ⟨walk⟩ := reachable
  obtain ⟨current, divergence⟩ := network.current_of_walk walk
  refine ⟨current, fun vertex => ?_⟩
  rw [divergence]
  by_cases atSource : vertex = source
  · subst vertex
    simp [distinct]
  · by_cases atSink : vertex = sink <;>
      simp_all [distinct, Ne.symm distinct]

theorem reachable_of_flow_nonempty (source sink : network.V)
    (flows : Nonempty (network.Flow source sink)) :
    network.toSimpleGraph.Reachable source sink := by
  classical
  by_contra disconnected
  obtain ⟨flow⟩ := flows
  let component : Finset network.V :=
    Finset.univ.filter (network.toSimpleGraph.Reachable source)
  have sourceMem : source ∈ component := by simp [component]
  have sinkNotMem : sink ∉ component := by simpa [component] using disconnected
  have endpointMembership (edge : network.E) :
      network.tail edge ∈ component ↔ network.head edge ∈ component := by
    by_cases same : network.tail edge = network.head edge
    · simp [same]
    · have adjacent : network.toSimpleGraph.Adj (network.tail edge) (network.head edge) :=
        ⟨same, Or.inl ⟨edge, rfl, rfl⟩⟩
      have joined := adjacent.reachable
      simp only [component, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun path => path.trans joined, fun path => path.trans joined.symm⟩
  have totalTransport : ∑ vertex ∈ component, network.div flow.val vertex = 1 := by
    have divergence : ∀ vertex, network.div flow.val vertex =
        (if vertex = source then 1 else if vertex = sink then -1 else 0) := flow.property
    simp_rw [divergence]
    rw [Finset.sum_eq_single source]
    · simp
    · intro vertex member notSource
      have notSink : vertex ≠ sink := by
        intro equality
        exact sinkNotMem (equality ▸ member)
      simp [notSource, notSink]
    · exact fun notMember => (notMember sourceMem).elim
  have zeroTransport : ∑ vertex ∈ component, network.div flow.val vertex = 0 := by
    rw [network.cut_divergence]
    apply Finset.sum_eq_zero
    intro edge _
    by_cases tailMem : network.tail edge ∈ component
    · have headMem := (endpointMembership edge).mp tailMem
      simp [tailMem, headMem]
    · have headNotMem : network.head edge ∉ component :=
        fun headMem => tailMem ((endpointMembership edge).mpr headMem)
      simp [tailMem, headNotMem]
  linarith

theorem flow_nonempty_iff_reachable (source sink : network.V) (distinct : source ≠ sink) :
    Nonempty (network.Flow source sink) ↔ network.toSimpleGraph.Reachable source sink :=
  ⟨network.reachable_of_flow_nonempty source sink,
    network.flow_nonempty_of_reachable source sink distinct⟩

/-- The full-domain electrical resistance of Definition `def:psi_Psi`.
For distinct terminals this is the actual extended Thomson infimum. -/
noncomputable def extendedEffRes (source sink : network.V) (resistances : Fin K → ℝ) : ℝ≥0∞ :=
  if source = sink then 0
  else ⨅ flow : network.Flow source sink, ENNReal.ofReal (network.energyNetwork flow.val resistances)

theorem extendedEffRes_self (source : network.V) (resistances : Fin K → ℝ) :
    network.extendedEffRes source source resistances = 0 := by
  simp [extendedEffRes]

theorem extendedEffRes_eq_iInf (source sink : network.V) (distinct : source ≠ sink)
    (resistances : Fin K → ℝ) :
    network.extendedEffRes source sink resistances =
      ⨅ flow : network.Flow source sink, ENNReal.ofReal (network.energyNetwork flow.val resistances) := by
  simp [extendedEffRes, distinct]

theorem extendedEffRes_eq_ofReal (source sink : network.V) (distinct : source ≠ sink)
    (flows : Nonempty (network.Flow source sink)) (resistances : Fin K → ℝ) :
    network.extendedEffRes source sink resistances =
      ENNReal.ofReal (network.effRes source sink flows resistances) := by
  letI := flows
  rw [network.extendedEffRes_eq_iInf source sink distinct,
    network.effRes_eq_iInf source sink flows, ENNReal.ofReal_iInf]

theorem extendedEffRes_eq_top_iff_not_reachable (source sink : network.V)
    (resistances : Fin K → ℝ) :
    network.extendedEffRes source sink resistances = ⊤ ↔
      ¬ network.toSimpleGraph.Reachable source sink := by
  by_cases same : source = sink
  · subst sink
    simp [network.extendedEffRes_self]
  · constructor
    · intro infinite reachable
      have flows := network.flow_nonempty_of_reachable source sink same reachable
      rw [network.extendedEffRes_eq_ofReal source sink same flows resistances] at infinite
      exact ENNReal.ofReal_ne_top infinite
    · intro disconnected
      have noFlows : ¬ Nonempty (network.Flow source sink) :=
        fun flows => disconnected (network.reachable_of_flow_nonempty source sink flows)
      letI : IsEmpty (network.Flow source sink) := not_nonempty_iff.mp noFlows
      simp [network.extendedEffRes_eq_iInf source sink same]

theorem extendedEffRes_ne_top_iff_reachable (source sink : network.V)
    (resistances : Fin K → ℝ) :
    network.extendedEffRes source sink resistances ≠ ⊤ ↔
      network.toSimpleGraph.Reachable source sink := by
  change ¬ (network.extendedEffRes source sink resistances = ⊤) ↔ _
  rw [network.extendedEffRes_eq_top_iff_not_reachable, not_not]

end EIGS.Network

namespace EIGS.RuleSystem

/-- The already-used connected real renormalisation coordinate is precisely
the finite branch of the new full-domain electrical definition. -/
theorem extendedEffRes_eq_toRenormMap {K : ℕ} (system : EIGS.RuleSystem K)
    (distinct : ∀ colour, system.βplus colour ≠ system.βminus colour)
    (resistances : Fin K → ℝ) (colour : Fin K) :
    (system.R colour).extendedEffRes (system.βplus colour) (system.βminus colour) resistances =
      ENNReal.ofReal (system.toRenormMap.apply resistances colour) := by
  exact (system.R colour).extendedEffRes_eq_ofReal _ _ (distinct colour)
    (system.connected colour) resistances

end EIGS.RuleSystem

#print axioms EIGS.Network.flow_nonempty_of_reachable
#print axioms EIGS.Network.reachable_of_flow_nonempty
#print axioms EIGS.Network.flow_nonempty_iff_reachable
#print axioms EIGS.Network.extendedEffRes_self
#print axioms EIGS.Network.extendedEffRes_eq_iInf
#print axioms EIGS.Network.extendedEffRes_eq_ofReal
#print axioms EIGS.Network.extendedEffRes_eq_top_iff_not_reachable
#print axioms EIGS.Network.extendedEffRes_ne_top_iff_reachable
#print axioms EIGS.RuleSystem.extendedEffRes_eq_toRenormMap
