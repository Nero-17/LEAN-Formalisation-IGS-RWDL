import RequestProject.Section2SimpleNetwork
import RequestProject.Section2Resistance

namespace EIGS.Network

open scoped BigOperators Classical

variable {K : ℕ} (network : Network K)

theorem isUnitFlow_of_div_on_erase (source sink : network.V) (source_ne_sink : source ≠ sink)
    (current : network.E → ℝ)
    (divergence : ∀ vertex ∈ Finset.univ.erase sink,
      network.div current vertex = if vertex = source then 1 else 0) :
    network.IsUnitFlow source sink current := by
  have sum_off_sink : (∑ vertex ∈ Finset.univ.erase sink, network.div current vertex) = 1 := by
    calc
      _ = ∑ vertex ∈ Finset.univ.erase sink, if vertex = source then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl divergence
      _ = 1 := by simp [source_ne_sink]
  have sum_all := Finset.sum_erase_add (Finset.univ : Finset network.V)
    (fun vertex => network.div current vertex) (Finset.mem_univ sink)
  have sink_divergence : network.div current sink = -1 := by
    rw [network.div_sum_zero current, sum_off_sink] at sum_all
    linarith
  intro vertex
  by_cases vertex_sink : vertex = sink
  · subst vertex
    simp [sink_divergence, source_ne_sink.symm]
  · have off_sink := divergence vertex (by simp [vertex_sink])
    simpa only [vertex_sink, if_false] using off_sink

/-- The oriented-edge Thomson resistance equals the resistance used by the
existing simple-walk Green function, under the explicit simple orientation
convention. Connectivity supplies the unit-flow existence proof. -/
theorem effRes_eq_simpleGraph_resistance (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (source_ne_sink : source ≠ sink) :
    network.effRes source sink
      (network.flow_nonempty_of_connected connected source sink source_ne_sink) (fun _ => 1) =
      EIGS.effResToBoundary network.toSimpleGraph (Finset.univ.erase sink) source := by
  have source_mem : source ∈ Finset.univ.erase sink := by simp [source_ne_sink]
  have complement_nonempty : (Finset.univ.erase sink)ᶜ.Nonempty := ⟨sink, by simp⟩
  have harmonic_is_flow := EIGS.harmonicFlow_isFlow network.toSimpleGraph connected
    complement_nonempty source_mem
  have restricted_unit_flow : network.IsUnitFlow source sink
      (fun edge => EIGS.harmonicFlow network.toSimpleGraph (Finset.univ.erase sink) source
        (network.tail edge) (network.head edge)) := by
    apply network.isUnitFlow_of_div_on_erase source sink source_ne_sink
    intro vertex vertex_mem
    rw [network.div_restrict_eq_simpleGraph loopless unique_edges _ harmonic_is_flow.1]
    exact harmonic_is_flow.2 vertex vertex_mem
  apply le_antisymm
  · calc
      _ ≤ network.energyNetwork
          (fun edge => EIGS.harmonicFlow network.toSimpleGraph (Finset.univ.erase sink) source
            (network.tail edge) (network.head edge)) (fun _ => 1) :=
        network.effRes_le_energy source sink _ (fun _ => zero_le_one)
          ⟨_, restricted_unit_flow⟩
      _ = EIGS.flowEnergy network.toSimpleGraph
          (EIGS.harmonicFlow network.toSimpleGraph (Finset.univ.erase sink) source) :=
        network.energy_restrict_eq_simpleGraph loopless unique_edges _ harmonic_is_flow.1
      _ = _ := EIGS.flowEnergy_harmonic network.toSimpleGraph _ _
  · apply network.le_effRes source sink
      (network.flow_nonempty_of_connected connected source sink source_ne_sink)
    intro current
    have pair_is_flow : EIGS.IsBoundaryUnitFlow network.toSimpleGraph
        (Finset.univ.erase sink) source (network.pairCurrent current.1) := by
      refine ⟨network.pairCurrent_antisymmetric current.1, ?_⟩
      intro vertex vertex_mem
      change (∑ neighbor, if network.toSimpleGraph.Adj vertex neighbor then
        network.pairCurrent current.1 vertex neighbor else 0) = _
      rw [network.div_pairCurrent loopless unique_edges]
      have vertex_ne_sink : vertex ≠ sink := (Finset.mem_erase.mp vertex_mem).1
      simpa only [vertex_ne_sink, if_false] using current.property vertex
    calc
      _ = EIGS.flowEnergy network.toSimpleGraph
          (EIGS.harmonicFlow network.toSimpleGraph (Finset.univ.erase sink) source) :=
        (EIGS.flowEnergy_harmonic network.toSimpleGraph _ _).symm
      _ ≤ EIGS.flowEnergy network.toSimpleGraph (network.pairCurrent current.1) :=
        EIGS.thomson_lower network.toSimpleGraph connected complement_nonempty source_mem pair_is_flow
      _ = _ := network.energy_pairCurrent loopless unique_edges current.1

theorem effRes_eq_simpleGraph_green_diagonal (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (source_ne_sink : source ≠ sink) :
    network.effRes source sink
      (network.flow_nonempty_of_connected connected source sink source_ne_sink) (fun _ => 1) =
      EIGS.greenFn network.toSimpleGraph (Finset.univ.erase sink)
        ⟨source, by simp [source_ne_sink]⟩ ⟨source, by simp [source_ne_sink]⟩ := by
  rw [network.effRes_eq_simpleGraph_resistance loopless unique_edges connected source sink source_ne_sink]
  exact EIGS.green_diag_eq_resistance network.toSimpleGraph connected
    ⟨sink, by simp⟩ (by simp [source_ne_sink])

end EIGS.Network
