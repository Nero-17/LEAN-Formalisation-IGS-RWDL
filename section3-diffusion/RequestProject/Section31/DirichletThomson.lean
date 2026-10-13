import RequestProject.Section2Substitution
import RequestProject.Section2FlowConnectivity
import RequestProject.Section31.Oscillation

/-!
# Potential energy and Thomson flow energy on the same finite network

The oriented edge set, its multiplicities and endpoint maps are unchanged.
Conductances are the reciprocals of the assigned positive resistances.
Discrete integration by parts and weighted Cauchy--Schwarz are proved for those
actual sums.  These are the finite-network bridge required to turn the
potential Dirichlet minimum into the reciprocal Thomson resistance.
-/

namespace EIGS.Network

open IGS.Sec31

variable {K : ℕ} (network : Network K)

noncomputable def potentialNetwork (resistances : Fin K → ℝ)
    (resistancesPositive : ∀ colour, 0 < resistances colour) : FiniteNetwork network.V where
  Edge := network.E
  fintypeEdge := network.fintypeE
  decEqEdge := Classical.decEq _
  ends := fun edge => (network.tail edge, network.head edge)
  cond := fun edge => (resistances (network.color edge))⁻¹
  cond_pos := fun edge => inv_pos.2 (resistancesPositive _)

/-- The Green identity for the unchanged oriented multigraph. -/
theorem sum_potential_mul_div (current : network.E → ℝ) (potential : network.V → ℝ) :
    (∑ vertex, potential vertex * network.div current vertex) =
      ∑ edge, current edge * (potential (network.tail edge) - potential (network.head edge)) := by
  calc
    (∑ vertex, potential vertex * network.div current vertex) =
        (∑ vertex, ∑ edge, if network.tail edge = vertex then potential vertex * current edge else 0) -
          ∑ vertex, ∑ edge, if network.head edge = vertex then potential vertex * current edge else 0 := by
      simp only [Network.div, mul_sub, Finset.mul_sum, mul_ite, mul_zero, Finset.sum_sub_distrib]
    _ = (∑ edge, ∑ vertex, if network.tail edge = vertex then potential vertex * current edge else 0) -
          ∑ edge, ∑ vertex, if network.head edge = vertex then potential vertex * current edge else 0 := by
      congr 1 <;> exact Finset.sum_comm
    _ = ∑ edge, current edge *
        (potential (network.tail edge) - potential (network.head edge)) := by
      simp [Finset.sum_ite_eq', eq_comm, Finset.sum_sub_distrib, mul_sub, mul_comm]

theorem sum_current_mul_potential_difference_of_unitFlow
    (source sink : network.V) (sourceNeSink : source ≠ sink)
    (current : network.Flow source sink) (potential : network.V → ℝ) :
    (∑ edge, current.val edge * (potential (network.tail edge) - potential (network.head edge))) =
      potential source - potential sink := by
  rw [← network.sum_potential_mul_div]
  have divergence : ∀ vertex, network.div current.val vertex =
      if vertex = source then 1 else if vertex = sink then -1 else 0 := current.property
  have summandEquality : ∀ vertex, potential vertex * network.div current.val vertex =
      (if vertex = source then potential source else 0) -
        (if vertex = sink then potential sink else 0) := by
    intro vertex
    rw [divergence]
    by_cases vertexSource : vertex = source
    · subst vertex
      simp [sourceNeSink]
    · by_cases vertexSink : vertex = sink
      · subst vertex
        simp [sourceNeSink.symm]
      · simp [vertexSource, vertexSink]
  simp_rw [summandEquality]
  simp [Finset.sum_sub_distrib]

/-- Weighted Cauchy--Schwarz with the actual resistance and conductance sums. -/
theorem potential_difference_sq_le_flow_energy_mul_potential_energy
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (source sink : network.V) (sourceNeSink : source ≠ sink)
    (current : network.Flow source sink) (potential : network.V → ℝ) :
    (potential source - potential sink) ^ 2 ≤
      network.energyNetwork current.val resistances *
        (network.potentialNetwork resistances resistancesPositive).energy potential := by
  have weightedCauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (s := Finset.univ)
    (r := fun edge => current.val edge *
      (potential (network.tail edge) - potential (network.head edge)))
    (f := fun edge => resistances (network.color edge) * (current.val edge) ^ 2)
    (g := fun edge => (resistances (network.color edge))⁻¹ *
      (potential (network.tail edge) - potential (network.head edge)) ^ 2)
    (fun edge _ => mul_nonneg (resistancesPositive _).le (sq_nonneg _))
    (fun edge _ => mul_nonneg (inv_pos.2 (resistancesPositive _)).le (sq_nonneg _))
    (by
      intro edge _
      field_simp [(resistancesPositive (network.color edge)).ne'])
  rw [network.sum_current_mul_potential_difference_of_unitFlow source sink sourceNeSink current potential]
    at weightedCauchy
  exact weightedCauchy

noncomputable def potentialGradientCurrent (resistances : Fin K → ℝ)
    (potential : network.V → ℝ) : network.E → ℝ :=
  fun edge => (resistances (network.color edge))⁻¹ *
    (potential (network.tail edge) - potential (network.head edge))

theorem div_potentialGradientCurrent_eq_grad
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (potential : network.V → ℝ) (vertex : network.V) :
    network.div (network.potentialGradientCurrent resistances potential) vertex =
      (network.potentialNetwork resistances resistancesPositive).grad potential vertex := by
  simp only [Network.div, potentialGradientCurrent, FiniteNetwork.grad,
    FiniteNetwork.inc, potentialNetwork, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  split_ifs <;> ring

theorem potential_energy_eq_sum_potential_mul_gradient_div
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (potential : network.V → ℝ) :
    (network.potentialNetwork resistances resistancesPositive).energy potential =
      ∑ vertex, potential vertex *
        network.div (network.potentialGradientCurrent resistances potential) vertex := by
  rw [network.sum_potential_mul_div]
  simp only [potentialGradientCurrent, potentialNetwork, FiniteNetwork.energy]
  apply Finset.sum_congr rfl
  intro edge _
  ring

private theorem sum_eq_two_terminals (source sink : network.V) (sourceNeSink : source ≠ sink)
    (values : network.V → ℝ)
    (valuesVanish : ∀ vertex, vertex ≠ source → vertex ≠ sink → values vertex = 0) :
    (∑ vertex, values vertex) = values source + values sink := by
  classical
  calc
    (∑ vertex, values vertex) = ∑ vertex ∈ ({source, sink} : Finset network.V), values vertex := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro vertex _ notTerminal
      have notEither : vertex ≠ source ∧ vertex ≠ sink := by simpa using notTerminal
      exact valuesVanish vertex notEither.1 notEither.2
    _ = values source + values sink := by rw [Finset.sum_pair sourceNeSink]

theorem potential_energy_pos_of_boundary_unit
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (source sink : network.V) (sourceNeSink : source ≠ sink)
    (flowExists : Nonempty (network.Flow source sink)) (potential : network.V → ℝ)
    (sourceValue : potential source = 1) (sinkValue : potential sink = 0) :
    0 < (network.potentialNetwork resistances resistancesPositive).energy potential := by
  obtain ⟨current⟩ := flowExists
  have weightedBound := network.potential_difference_sq_le_flow_energy_mul_potential_energy
    resistances resistancesPositive source sink sourceNeSink current potential
  rw [sourceValue, sinkValue] at weightedBound
  have energyNonnegative := (network.potentialNetwork resistances resistancesPositive).energy_nonneg potential
  by_contra notPositive
  have energyZero : (network.potentialNetwork resistances resistancesPositive).energy potential = 0 :=
    le_antisymm (not_lt.1 notPositive) energyNonnegative
  norm_num [energyZero] at weightedBound

theorem gradient_div_source_eq_energy_of_min
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (source sink : network.V) (sourceNeSink : source ≠ sink)
    (potential : network.V → ℝ) (sourceValue : potential source = 1) (sinkValue : potential sink = 0)
    (potentialMinimal : ∀ competitor : network.V → ℝ,
      competitor source = 1 → competitor sink = 0 →
        (network.potentialNetwork resistances resistancesPositive).energy potential ≤
          (network.potentialNetwork resistances resistancesPositive).energy competitor) :
    network.div (network.potentialGradientCurrent resistances potential) source =
      (network.potentialNetwork resistances resistancesPositive).energy potential := by
  classical
  have harmonicInterior : ∀ vertex, vertex ≠ source → vertex ≠ sink →
      network.div (network.potentialGradientCurrent resistances potential) vertex = 0 := by
    intro vertex vertexNeSource vertexNeSink
    rw [network.div_potentialGradientCurrent_eq_grad resistances resistancesPositive]
    apply (network.potentialNetwork resistances resistancesPositive).grad_eq_zero_of_min
      {source, sink} potential potential
    · intro competitor competitorBoundary
      apply potentialMinimal competitor
      · simpa [sourceValue] using competitorBoundary source (by simp)
      · simpa [sinkValue] using competitorBoundary sink (by simp)
    · intro _ _; rfl
    · simp [vertexNeSource, vertexNeSink]
  rw [network.potential_energy_eq_sum_potential_mul_gradient_div]
  rw [network.sum_eq_two_terminals source sink sourceNeSink
    (fun vertex => potential vertex * network.div (network.potentialGradientCurrent resistances potential) vertex)
    (fun vertex vertexNeSource vertexNeSink => by
      simpa only [harmonicInterior vertex vertexNeSource vertexNeSink, mul_zero])]
  rw [sourceValue, sinkValue]
  ring

noncomputable def normalizedPotentialCurrent (resistances : Fin K → ℝ)
    (resistancesPositive : ∀ colour, 0 < resistances colour) (potential : network.V → ℝ) :
    network.E → ℝ :=
  fun edge => ((network.potentialNetwork resistances resistancesPositive).energy potential)⁻¹ *
    network.potentialGradientCurrent resistances potential edge

theorem normalizedPotentialCurrent_isUnitFlow
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (source sink : network.V) (sourceNeSink : source ≠ sink)
    (flowExists : Nonempty (network.Flow source sink)) (potential : network.V → ℝ)
    (sourceValue : potential source = 1) (sinkValue : potential sink = 0)
    (potentialMinimal : ∀ competitor : network.V → ℝ,
      competitor source = 1 → competitor sink = 0 →
        (network.potentialNetwork resistances resistancesPositive).energy potential ≤
          (network.potentialNetwork resistances resistancesPositive).energy competitor) :
    network.IsUnitFlow source sink
      (network.normalizedPotentialCurrent resistances resistancesPositive potential) := by
  classical
  have harmonicInterior : ∀ vertex, vertex ≠ source → vertex ≠ sink →
      network.div (network.potentialGradientCurrent resistances potential) vertex = 0 := by
    intro vertex vertexNeSource vertexNeSink
    rw [network.div_potentialGradientCurrent_eq_grad resistances resistancesPositive]
    apply (network.potentialNetwork resistances resistancesPositive).grad_eq_zero_of_min
      {source, sink} potential potential
    · intro competitor competitorBoundary
      apply potentialMinimal competitor
      · simpa [sourceValue] using competitorBoundary source (by simp)
      · simpa [sinkValue] using competitorBoundary sink (by simp)
    · intro _ _; rfl
    · simp [vertexNeSource, vertexNeSink]
  have divergenceSource := network.gradient_div_source_eq_energy_of_min resistances
    resistancesPositive source sink sourceNeSink potential sourceValue sinkValue potentialMinimal
  have divergenceSum := network.div_sum_zero (network.potentialGradientCurrent resistances potential)
  rw [network.sum_eq_two_terminals source sink sourceNeSink _ harmonicInterior, divergenceSource]
    at divergenceSum
  have divergenceSink : network.div (network.potentialGradientCurrent resistances potential) sink =
      -(network.potentialNetwork resistances resistancesPositive).energy potential := by linarith
  have energyPositive := network.potential_energy_pos_of_boundary_unit resistances resistancesPositive
    source sink sourceNeSink flowExists potential sourceValue sinkValue
  intro vertex
  change network.div (fun edge =>
    ((network.potentialNetwork resistances resistancesPositive).energy potential)⁻¹ *
      network.potentialGradientCurrent resistances potential edge) vertex = _
  rw [network.div_smul]
  by_cases vertexSource : vertex = source
  · subst vertex
    simp [divergenceSource, energyPositive.ne']
  · by_cases vertexSink : vertex = sink
    · subst vertex
      simp [vertexSource, divergenceSink, energyPositive.ne']
    · simp [vertexSource, vertexSink, harmonicInterior vertex vertexSource vertexSink]

theorem normalizedPotentialCurrent_energy
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (potential : network.V → ℝ)
    (energyPositive : 0 < (network.potentialNetwork resistances resistancesPositive).energy potential) :
    network.energyNetwork (network.normalizedPotentialCurrent resistances resistancesPositive potential)
      resistances = ((network.potentialNetwork resistances resistancesPositive).energy potential)⁻¹ := by
  calc
    network.energyNetwork (network.normalizedPotentialCurrent resistances resistancesPositive potential)
        resistances =
      ((network.potentialNetwork resistances resistancesPositive).energy potential)⁻¹ ^ 2 *
        (network.potentialNetwork resistances resistancesPositive).energy potential := by
      simp only [Network.energyNetwork, normalizedPotentialCurrent, potentialGradientCurrent,
        FiniteNetwork.energy, potentialNetwork, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro edge _
      field_simp [(resistancesPositive (network.color edge)).ne']
    _ = ((network.potentialNetwork resistances resistancesPositive).energy potential)⁻¹ := by
      field_simp [energyPositive.ne']

/-- The missing one-cell value: the potential minimum is the reciprocal of
Thomson's resistance, proved on the actual finite multigraph. -/
theorem effRes_eq_inverse_minimum_potential_energy
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (source sink : network.V) (sourceNeSink : source ≠ sink)
    (flowExists : Nonempty (network.Flow source sink)) (potential : network.V → ℝ)
    (sourceValue : potential source = 1) (sinkValue : potential sink = 0)
    (potentialMinimal : ∀ competitor : network.V → ℝ,
      competitor source = 1 → competitor sink = 0 →
        (network.potentialNetwork resistances resistancesPositive).energy potential ≤
          (network.potentialNetwork resistances resistancesPositive).energy competitor) :
    network.effRes source sink flowExists resistances =
      ((network.potentialNetwork resistances resistancesPositive).energy potential)⁻¹ := by
  have energyPositive := network.potential_energy_pos_of_boundary_unit resistances resistancesPositive
    source sink sourceNeSink flowExists potential sourceValue sinkValue
  apply le_antisymm
  · let normalizedFlow : network.Flow source sink :=
      ⟨network.normalizedPotentialCurrent resistances resistancesPositive potential,
        network.normalizedPotentialCurrent_isUnitFlow resistances resistancesPositive source sink
          sourceNeSink flowExists potential sourceValue sinkValue potentialMinimal⟩
    exact (network.effRes_le_energy source sink flowExists (fun colour => (resistancesPositive colour).le)
      normalizedFlow).trans_eq (by
        exact network.normalizedPotentialCurrent_energy resistances resistancesPositive potential energyPositive)
  · apply network.le_effRes source sink flowExists
    intro current
    have weightedBound := network.potential_difference_sq_le_flow_energy_mul_potential_energy
      resistances resistancesPositive source sink sourceNeSink current potential
    rw [sourceValue, sinkValue] at weightedBound
    rw [inv_eq_one_div]
    apply (div_le_iff₀ energyPositive).2
    nlinarith

/-- Connectivity supplies a genuine Poincaré constant via the finitely many
unit-flow energies, with no separate analytic bound assumed. -/
theorem exists_potential_poincare_constant
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (boundaryVertex : network.V)
    (connected : network.toSimpleGraph.Connected) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ potential : network.V → ℝ,
      potential boundaryVertex = 0 → ∀ vertex,
        (potential vertex) ^ 2 ≤
          bound * (network.potentialNetwork resistances resistancesPositive).energy potential := by
  classical
  have currentExists : ∀ vertex, vertex ≠ boundaryVertex →
      Nonempty (network.Flow vertex boundaryVertex) := fun vertex vertexDistinct =>
    network.flow_nonempty_of_connected connected vertex boundaryVertex vertexDistinct
  let flowCost : network.V → ℝ := fun vertex =>
    if vertexEqual : vertex = boundaryVertex then 0
    else network.energyNetwork (Classical.choice (currentExists vertex vertexEqual)).val resistances
  have costNonnegative : ∀ vertex, 0 ≤ flowCost vertex := by
    intro vertex
    by_cases vertexEqual : vertex = boundaryVertex
    · simp [flowCost, vertexEqual]
    · simp only [flowCost, vertexEqual, dite_false]
      exact network.energyNetwork_nonneg _ (fun colour => (resistancesPositive colour).le)
  refine ⟨∑ vertex, flowCost vertex, Finset.sum_nonneg (fun vertex _ => costNonnegative vertex), ?_⟩
  intro potential boundaryZero vertex
  by_cases vertexEqual : vertex = boundaryVertex
  · subst vertex
    rw [boundaryZero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg (Finset.sum_nonneg (fun vertex _ => costNonnegative vertex))
      ((network.potentialNetwork resistances resistancesPositive).energy_nonneg potential)
  · have potentialBound := network.potential_difference_sq_le_flow_energy_mul_potential_energy
      resistances resistancesPositive vertex boundaryVertex vertexEqual
      (Classical.choice (currentExists vertex vertexEqual)) potential
    rw [boundaryZero, sub_zero] at potentialBound
    have vertexCostBound : flowCost vertex ≤ ∑ otherVertex, flowCost otherVertex :=
      Finset.single_le_sum (fun otherVertex _ => costNonnegative otherVertex) (Finset.mem_univ vertex)
    have potentialEnergyNonnegative :=
      (network.potentialNetwork resistances resistancesPositive).energy_nonneg potential
    exact potentialBound.trans (by
      simpa only [flowCost, vertexEqual, dite_false] using
        mul_le_mul_of_nonneg_right vertexCostBound potentialEnergyNonnegative)

/-- The complete finite-network minimum/value theorem, from graph connectivity
and positive edge resistances only. -/
theorem exists_minimum_potential_energy_eq_inverse_effRes
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (sourceNeSink : source ≠ sink) :
    ∃ potential : network.V → ℝ,
      potential source = 1 ∧ potential sink = 0 ∧
      (∀ competitor : network.V → ℝ, competitor source = 1 → competitor sink = 0 →
        (network.potentialNetwork resistances resistancesPositive).energy potential ≤
          (network.potentialNetwork resistances resistancesPositive).energy competitor) ∧
      (network.potentialNetwork resistances resistancesPositive).energy potential =
        (network.effRes source sink
          (network.flow_nonempty_of_connected connected source sink sourceNeSink) resistances)⁻¹ := by
  classical
  obtain ⟨bound, boundNonnegative, poincareBound⟩ :=
    network.exists_potential_poincare_constant resistances resistancesPositive source connected
  obtain ⟨potential, potentialBoundary, minimum⟩ :=
    (network.potentialNetwork resistances resistancesPositive).exists_min {source, sink}
      (fun vertex => if vertex = source then 1 else 0) bound boundNonnegative
      (fun values boundaryZero vertex =>
        poincareBound values (boundaryZero source (by simp)) vertex)
  have sourceValue : potential source = 1 := by
    simpa using potentialBoundary source (by simp)
  have sinkValue : potential sink = 0 := by
    simpa [sourceNeSink.symm] using potentialBoundary sink (by simp)
  have potentialMinimal : ∀ competitor : network.V → ℝ,
      competitor source = 1 → competitor sink = 0 →
        (network.potentialNetwork resistances resistancesPositive).energy potential ≤
          (network.potentialNetwork resistances resistancesPositive).energy competitor := by
    intro competitor competitorSource competitorSink
    apply minimum competitor
    intro vertex terminal
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using terminal :
      vertex = source ∨ vertex = sink) with vertexSource | vertexSink
    · subst vertex
      simpa using competitorSource
    · subst vertex
      simpa [sourceNeSink.symm] using competitorSink
  refine ⟨potential, sourceValue, sinkValue, potentialMinimal, ?_⟩
  rw [network.effRes_eq_inverse_minimum_potential_energy resistances resistancesPositive
    source sink sourceNeSink (network.flow_nonempty_of_connected connected source sink sourceNeSink)
    potential sourceValue sinkValue potentialMinimal, inv_inv]

/-- Arbitrary prescribed terminal values are obtained by the actual affine
harmonic extension, with the full one-cell Dirichlet minimum value. -/
theorem exists_minimum_potential_energy_terminal_values
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (sourceNeSink : source ≠ sink) (sourceValue sinkValue : ℝ) :
    ∃ potential : network.V → ℝ,
      potential source = sourceValue ∧ potential sink = sinkValue ∧
      (∀ competitor : network.V → ℝ, competitor source = sourceValue → competitor sink = sinkValue →
        (network.potentialNetwork resistances resistancesPositive).energy potential ≤
          (network.potentialNetwork resistances resistancesPositive).energy competitor) ∧
      (network.potentialNetwork resistances resistancesPositive).energy potential =
        (sourceValue - sinkValue) ^ 2 *
          (network.effRes source sink
            (network.flow_nonempty_of_connected connected source sink sourceNeSink) resistances)⁻¹ := by
  classical
  obtain ⟨profile, profileSource, profileSink, profileMinimal, profileEnergy⟩ :=
    network.exists_minimum_potential_energy_eq_inverse_effRes resistances resistancesPositive
      connected source sink sourceNeSink
  refine ⟨fun vertex => sinkValue + (sourceValue - sinkValue) * profile vertex, ?_, ?_, ?_, ?_⟩
  · simp only [profileSource]; ring
  · simp only [profileSink]; ring
  · intro competitor competitorSource competitorSink
    apply (network.potentialNetwork resistances resistancesPositive).min_affine
      {source, sink} profile profile sinkValue (sourceValue - sinkValue)
    · intro trial trialBoundary
      apply profileMinimal trial
      · simpa [profileSource] using trialBoundary source (by simp)
      · simpa [profileSink] using trialBoundary sink (by simp)
    · intro vertex terminal
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using terminal :
        vertex = source ∨ vertex = sink) with vertexSource | vertexSink
      · subst vertex
        rw [competitorSource, profileSource]
        ring
      · subst vertex
        rw [competitorSink, profileSink]
        ring
  · rw [FiniteNetwork.energy_affine, profileEnergy]

end EIGS.Network
