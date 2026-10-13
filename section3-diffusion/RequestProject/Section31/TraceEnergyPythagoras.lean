import RequestProject.Section31.TraceQuadraticForm
import RequestProject.Section31.EnergyOrthogonality

/-! An attained finite trace gives exact energy Pythagoras on the constructed
finite-energy domain. The proof derives all fine-level minima and passes the
proved finite edge-energy identity to the increasing-energy limit. -/

namespace IGS.Sec31

open Filter Topology

variable {Vertex : Type*}

theorem finite_energy_le_traceEnergyValue (networks : ℕ → FiniteNetwork Vertex)
    (values : traceEnergyDomain networks) (level : ℕ) :
    (networks level).energy values ≤ traceEnergyValue networks values := by
  rw [traceEnergyValue_eq_iSup]
  obtain ⟨bound, boundValid⟩ := values.property
  exact le_ciSup ⟨bound, by
    rintro _ ⟨index, rfl⟩
    exact boundValid index⟩ level

theorem traceEnergyValue_pythagoras_of_attained_trace
    (networks : ℕ → FiniteNetwork Vertex)
    (energyIncreasing : ∀ values : Vertex → ℝ,
      Monotone (fun level => (networks level).energy values))
    (boundary : Set Vertex) (coarseLevel : ℕ)
    (coarseEndpoints : ∀ edge : (networks coarseLevel).Edge,
      ((networks coarseLevel).ends edge).1 ∈ boundary ∧
        ((networks coarseLevel).ends edge).2 ∈ boundary)
    (harmonic target : traceEnergyDomain networks)
    (attainedTrace : traceEnergyValue networks harmonic = (networks coarseLevel).energy harmonic)
    (targetBoundary : ∀ vertex ∈ boundary, target.val vertex = harmonic.val vertex) :
    traceEnergyValue networks target =
      traceEnergyValue networks harmonic + traceEnergyValue networks (target - harmonic) := by
  have coarseEnergy_eq_of_boundary (competitor : Vertex → ℝ)
      (competitorBoundary : ∀ vertex ∈ boundary, competitor vertex = harmonic.val vertex) :
      (networks coarseLevel).energy competitor = (networks coarseLevel).energy harmonic := by
    unfold FiniteNetwork.energy
    apply Finset.sum_congr rfl
    intro edge _
    rw [competitorBoundary _ (coarseEndpoints edge).1,
      competitorBoundary _ (coarseEndpoints edge).2]
  have finePythagoras : ∀ level, coarseLevel ≤ level →
      (networks level).energy target = (networks level).energy harmonic +
        (networks level).energy (target - harmonic) := by
    intro level afterCoarse
    apply (networks level).energy_sub_of_min boundary harmonic harmonic
      (fun _ _ => rfl) _ target targetBoundary
    intro competitor competitorBoundary
    calc
      (networks level).energy harmonic ≤ traceEnergyValue networks harmonic :=
        finite_energy_le_traceEnergyValue networks harmonic level
      _ = (networks coarseLevel).energy harmonic := attainedTrace
      _ = (networks coarseLevel).energy competitor :=
        (coarseEnergy_eq_of_boundary competitor competitorBoundary).symm
      _ ≤ (networks level).energy competitor := energyIncreasing competitor afterCoarse
  apply tendsto_nhds_unique (finite_energy_tendsto_traceEnergyValue networks energyIncreasing target)
  apply ((finite_energy_tendsto_traceEnergyValue networks energyIncreasing harmonic).add
    (finite_energy_tendsto_traceEnergyValue networks energyIncreasing (target - harmonic))).congr'
  filter_upwards [eventually_ge_atTop coarseLevel] with level afterCoarse
  exact (finePythagoras level afterCoarse).symm

end IGS.Sec31
