import RequestProject.Section2SimpleResistance
import RequestProject.Section2RandomWalk

namespace EIGS.Network

open scoped BigOperators Classical

variable {K : ℕ} (network : Network K)

theorem unitPotential_laplacian (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (source_ne_sink : source ≠ sink) :
    (network.toSimpleGraph.lapMatrix ℝ).mulVec
      (EIGS.unitPotential network.toSimpleGraph (Finset.univ.erase sink) source) =
      fun vertex => (if vertex = source then (1 : ℝ) else 0) -
        (if vertex = sink then 1 else 0) := by
  have source_mem : source ∈ Finset.univ.erase sink := by simp [source_ne_sink]
  have harmonic_is_flow := EIGS.harmonicFlow_isFlow network.toSimpleGraph connected
    (show (Finset.univ.erase sink)ᶜ.Nonempty from ⟨sink, by simp⟩) source_mem
  have unit_flow : network.IsUnitFlow source sink
      (fun edge => EIGS.harmonicFlow network.toSimpleGraph (Finset.univ.erase sink) source
        (network.tail edge) (network.head edge)) := by
    apply network.isUnitFlow_of_div_on_erase source sink source_ne_sink
    intro vertex vertex_mem
    rw [network.div_restrict_eq_simpleGraph loopless unique_edges _ harmonic_is_flow.1]
    exact harmonic_is_flow.2 vertex vertex_mem
  ext vertex
  have divergence := unit_flow vertex
  rw [network.div_restrict_eq_simpleGraph loopless unique_edges _ harmonic_is_flow.1] at divergence
  change EIGS.flowDiv network.toSimpleGraph
    (fun first second => EIGS.unitPotential network.toSimpleGraph (Finset.univ.erase sink) source first -
      EIGS.unitPotential network.toSimpleGraph (Finset.univ.erase sink) source second) vertex = _ at divergence
  rw [EIGS.flowDiv_gradient] at divergence
  by_cases vertex_source : vertex = source <;> by_cases vertex_sink : vertex = sink <;>
    simp_all

/-- The honestly defined simple-walk commute time has the same resistance
factor as the oriented-edge Thomson construction. -/
theorem commute_eq_mass_mul_effRes (loopless : network.Loopless)
    (unique_edges : network.EdgesUnique) (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (source_ne_sink : source ≠ sink) :
    EIGS.expExit network.toSimpleGraph ({sink}ᶜ) source +
        EIGS.expExit network.toSimpleGraph ({source}ᶜ) sink =
      2 * (Fintype.card network.E : ℝ) * network.effRes source sink
        (network.flow_nonempty_of_connected connected source sink source_ne_sink) (fun _ => 1) := by
  have source_mem : source ∈ Finset.univ.erase sink := by simp [source_ne_sink]
  have potential_drop :
      EIGS.unitPotential network.toSimpleGraph (Finset.univ.erase sink) source source -
        EIGS.unitPotential network.toSimpleGraph (Finset.univ.erase sink) source sink =
      EIGS.effResToBoundary network.toSimpleGraph (Finset.univ.erase sink) source := by
    rw [EIGS.green_diag_eq_resistance network.toSimpleGraph connected
      (show (Finset.univ.erase sink)ᶜ.Nonempty from ⟨sink, by simp⟩) source_mem]
    simp [EIGS.unitPotential, source_mem]
  have commute := EIGS.commute_eq_two_card_edges_mul_resistance network.toSimpleGraph connected
    (EIGS.hittingSystem_expHit connected source) (EIGS.hittingSystem_expHit connected sink)
    (network.unitPotential_laplacian loopless unique_edges connected source sink source_ne_sink)
  rw [potential_drop, ← network.effRes_eq_simpleGraph_resistance loopless unique_edges connected
    source sink source_ne_sink, ← network.card_edges_eq_simpleGraph loopless unique_edges] at commute
  exact commute

end EIGS.Network
