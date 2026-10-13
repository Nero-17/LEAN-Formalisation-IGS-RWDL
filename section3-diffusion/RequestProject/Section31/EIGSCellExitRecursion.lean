import RequestProject.Section31.EIGSSkeletonConductance
import RequestProject.Section2UnitTraceComposition
import RequestProject.Section2ExitVoltage

/-!
Actual durations between distinct coarse-skeleton vertices. The star
voltage is identified internally with the true first-hitting probability.
The time identity will use finite Green symmetry, not a prescribed strong
Markov or exit-time bound. Cell localization and the layer recursion remain
separate obligations until their actual graph interfaces are constructed.
-/

namespace EIGS

open scoped BigOperators Classical
open Matrix IGS.Sec31

variable {K : ℕ}

/-- The actual first-hitting probability of the distinguished coarse
vertex is exactly the voltage of its genuine incident star. -/
theorem xiSkeletonHitting_eq_star_voltage (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (center : XiVtx system coarse)
    (vertex : XiVtx system (coarse + steps)) :
    hitDistLim (xiGraphWalkChain system rule_connected (coarse + steps))
        (Finset.univ.image (xiForward system coarse steps)) vertex
        (xiForward system coarse steps center) =
      boundaryVoltageProfile (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center)
        (xiForward system coarse steps center) vertex := by
  rw [xiGraphWalkChain_first_hitting_eq_trace system rule_connected rules_loopless rules_unique
    planting_nonadjacent coarse steps center vertex]
  rw [xiUnitTraceExtension_eq_potentialValues]
  exact (congrFun (xiIncidentStar_boundaryVoltageProfile_eq_potentialValues system rule_connected
    rules_loopless rules_unique planting_nonadjacent coarse steps center) vertex).symm

theorem xiSkeletonReturnProbability_self_eq_voltage_average (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (center : XiVtx system coarse) :
    xiSkeletonReturnProbability system rule_connected coarse steps center center =
      ∑ vertex : XiVtx system (coarse + steps),
        transProb (XiSimpleGraph system (coarse + steps))
          (xiForward system coarse steps center) vertex *
        boundaryVoltageProfile (XiSimpleGraph system (coarse + steps))
          (xiIncidentStarDomain system coarse steps center)
          (xiForward system coarse steps center) vertex := by
  unfold xiSkeletonReturnProbability
  apply Finset.sum_congr rfl
  intro vertex _
  rw [xiSkeletonHitting_eq_star_voltage system rule_connected rules_loopless rules_unique
    planting_nonadjacent coarse steps center vertex]

/-- One original step plus the actual mean time to return to any coarse
skeleton vertex; returns to the starting skeleton vertex are retained. -/
noncomputable def xiSkeletonReturnDuration (system : EIGSData K)
    (coarse steps : ℕ) (center : XiVtx system coarse) : ℝ :=
  1 + ∑ vertex : XiVtx system (coarse + steps),
    transProb (XiSimpleGraph system (coarse + steps))
      (xiForward system coarse steps center) vertex *
    expExit (XiSimpleGraph system (coarse + steps))
      (Finset.univ.image (xiForward system coarse steps))ᶜ vertex

theorem xiSkeletonReturnDuration_nonnegative (system : EIGSData K)
    (coarse steps : ℕ) (center : XiVtx system coarse) :
    0 ≤ xiSkeletonReturnDuration system coarse steps center := by
  unfold xiSkeletonReturnDuration
  apply add_nonneg (by norm_num)
  exact Finset.sum_nonneg fun vertex _ =>
    mul_nonneg (transProb_nonneg _ _) (expExit_nonneg _)

/-- The native survival-series return duration is exactly the old finite
chain excursionTime, on the actual skeleton and original simple walk. -/
theorem xiSkeletonReturnDuration_eq_excursionTime (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) (center : XiVtx system coarse) :
    xiSkeletonReturnDuration system coarse steps center =
      excursionTime (xiGraphWalkChain system rule_connected (coarse + steps))
        (Finset.univ.image (xiForward system coarse steps))
        ⟨xiForward system coarse steps center,
          Finset.mem_image.mpr ⟨center, Finset.mem_univ _, rfl⟩⟩ := by
  unfold xiSkeletonReturnDuration excursionTime
  congr 1
  apply Finset.sum_congr rfl
  intro vertex _
  change transProb (XiSimpleGraph system (coarse + steps))
      (xiForward system coarse steps center) vertex * _ =
    transProb (XiSimpleGraph system (coarse + steps))
      (xiForward system coarse steps center) vertex * _
  congr 1
  symm
  exact graphWalkChain_hitTime (XiSimpleGraph system (coarse + steps))
    (xiSimpleGraph_connected system rule_connected _)
    (fun vertex => by exact_mod_cast xiSimpleGraph_degree_positive system rule_connected _ vertex)
    (Finset.univ.image (xiForward system coarse steps))
    (Finset.image_nonempty.mpr ⟨center, Finset.mem_univ _⟩) vertex

/-- Finite Green symmetry on the actual graph, with both quantities
expressed as the native simple-graph Laplacian pairing. -/
theorem laplacian_pairing_symmetric {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj] (first second : Vertex → ℝ) :
    (∑ vertex, first vertex * (graph.lapMatrix ℝ *ᵥ second) vertex) =
      ∑ vertex, second vertex * (graph.lapMatrix ℝ *ᵥ first) vertex := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro vertex _
  apply Finset.sum_congr rfl
  intro neighbour _
  have symmetric := (graph.isSymm_lapMatrix (R := ℝ)).apply vertex neighbour
  rw [symmetric]
  ring

/-- A harmonic indicator's degree mass is the degree at the distinguished
boundary vertex times the actual duration of one return excursion. -/
theorem harmonic_mass_eq_degree_mul_return_duration
    {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj] (connected : graph.Connected)
    (skeleton : Finset Vertex) (center : Vertex) (center_inside : center ∈ skeleton)
    (degree_positive : 0 < graph.degree center) (voltage : Vertex → ℝ)
    (voltage_boundary : ∀ vertex ∈ skeleton, voltage vertex = if vertex = center then 1 else 0)
    (voltage_harmonic : ∀ vertex, vertex ∉ skeleton →
      (graph.lapMatrix ℝ *ᵥ voltage) vertex = 0) :
    (∑ vertex, voltage vertex * (graph.degree vertex : ℝ)) =
      (graph.degree center : ℝ) *
        (1 + ∑ vertex, transProb graph center vertex * expExit graph skeletonᶜ vertex) := by
  let return_time := expExit graph skeletonᶜ
  let return_duration := 1 + ∑ vertex, transProb graph center vertex * return_time vertex
  have proper : (skeletonᶜ)ᶜ.Nonempty := by
    simpa using (show skeleton.Nonempty from ⟨center, center_inside⟩)
  have return_system := exitSystem_expExit connected proper
  have return_zero : ∀ vertex ∈ skeleton, return_time vertex = 0 := by
    intro vertex inside
    exact expExit_zero_of_notMem (by simpa using inside)
  have center_duration : (graph.degree center : ℝ) * return_duration =
      (graph.degree center : ℝ) + ∑ vertex ∈ graph.neighborFinset center, return_time vertex := by
    dsimp only [return_duration]
    rw [mul_add, mul_one, transProb_smul_sum degree_positive return_time]
    rw [mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr degree_positive.ne')]
  have reverse_pairing :
      (∑ vertex, return_time vertex * (graph.lapMatrix ℝ *ᵥ voltage) vertex) = 0 := by
    apply Finset.sum_eq_zero
    intro vertex _
    by_cases inside : vertex ∈ skeleton
    · rw [return_zero vertex inside, zero_mul]
    · rw [voltage_harmonic vertex inside, mul_zero]
  have pointwise : ∀ vertex,
      voltage vertex * (graph.lapMatrix ℝ *ᵥ return_time) vertex =
        voltage vertex * (graph.degree vertex : ℝ) -
          if vertex = center then (graph.degree center : ℝ) * return_duration else 0 := by
    intro vertex
    by_cases inside : vertex ∈ skeleton
    · rw [voltage_boundary vertex inside]
      by_cases equal : vertex = center
      · subst vertex
        rw [if_pos rfl, one_mul, one_mul, lapMatrix_mulVec_apply,
          return_zero center center_inside, mul_zero, zero_sub, center_duration]
        simp only [if_true]
        ring
      · simp only [if_neg equal, zero_mul, sub_zero]
    · have different : vertex ≠ center := by
        intro equal
        subst vertex
        exact inside center_inside
      rw [if_neg different, sub_zero]
      rw [return_system.2 vertex (Finset.mem_compl.mpr inside)]
  have forward_pairing :
      (∑ vertex, voltage vertex * (graph.lapMatrix ℝ *ᵥ return_time) vertex) =
        (∑ vertex, voltage vertex * (graph.degree vertex : ℝ)) -
          (graph.degree center : ℝ) * return_duration := by
    simp_rw [pointwise]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have symmetric := laplacian_pairing_symmetric graph voltage return_time
  rw [reverse_pairing, forward_pairing] at symmetric
  exact sub_eq_zero.mp symmetric

/-- The mass identity above on the actual incident star and its actual
coarse-skeleton return duration. The true voltage boundary data and its
harmonicity are supplied by the proved first-hitting identification. -/
theorem xiSkeletonReturnDuration_mul_degree_eq_voltage_mass (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (center : XiVtx system coarse) :
    ((XiSimpleGraph system (coarse + steps)).degree
        (xiForward system coarse steps center) : ℝ) * xiSkeletonReturnDuration system coarse steps center =
      ∑ vertex : XiVtx system (coarse + steps),
        boundaryVoltageProfile (XiSimpleGraph system (coarse + steps))
          (xiIncidentStarDomain system coarse steps center)
          (xiForward system coarse steps center) vertex *
        ((XiSimpleGraph system (coarse + steps)).degree vertex : ℝ) := by
  symm
  apply harmonic_mass_eq_degree_mul_return_duration
    (XiSimpleGraph system (coarse + steps)) (xiSimpleGraph_connected system rule_connected _)
    (Finset.univ.image (xiForward system coarse steps)) (xiForward system coarse steps center)
    (Finset.mem_image.mpr ⟨center, Finset.mem_univ _, rfl⟩)
    (by
      exact_mod_cast xiSimpleGraph_degree_positive system rule_connected (coarse + steps)
        (xiForward system coarse steps center))
  · intro vertex membership
    rw [← xiSkeletonHitting_eq_star_voltage system rule_connected rules_loopless rules_unique
      planting_nonadjacent coarse steps center vertex]
    exact hitDistLim_of_mem _ _ membership _
  · intro vertex outside
    have voltage_eq := funext (xiSkeletonHitting_eq_star_voltage system rule_connected rules_loopless
      rules_unique planting_nonadjacent coarse steps center)
    rw [← voltage_eq]
    exact graphWalkChain_first_hitting_harmonic (XiSimpleGraph system (coarse + steps))
      (fun vertex => by exact_mod_cast xiSimpleGraph_degree_positive system rule_connected _ vertex)
      _ _ outside

theorem boundaryVoltageProfile_laplacian_source
    {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj] (connected : graph.Connected)
    {domain : Finset Vertex} (proper : domainᶜ.Nonempty) {source : Vertex} (inside : source ∈ domain) :
    (graph.lapMatrix ℝ *ᵥ boundaryVoltageProfile graph domain source) source =
      (effResToBoundary graph domain source)⁻¹ := by
  change (graph.lapMatrix ℝ *ᵥ
      ((effResToBoundary graph domain source)⁻¹ • unitPotential graph domain source)) source = _
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul,
    lapMatrix_mulVec_unitPotential graph connected proper inside source inside,
    if_true, mul_one]

/-- The actual return escape probability is the star capacity divided by
the actual fine degree. All voltage and kernel identifications are filled
by the already constructed actual walk and actual incident star. -/
theorem xiSkeletonReturnProbability_escape_capacity (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (center : XiVtx system coarse) :
    ((XiSimpleGraph system (coarse + steps)).degree (xiForward system coarse steps center) : ℝ) *
        (1 - xiSkeletonReturnProbability system rule_connected coarse steps center center) =
      (effResToBoundary (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center)
        (xiForward system coarse steps center))⁻¹ := by
  let voltage := boundaryVoltageProfile (XiSimpleGraph system (coarse + steps))
    (xiIncidentStarDomain system coarse steps center) (xiForward system coarse steps center)
  have degree_positive : 0 < (XiSimpleGraph system (coarse + steps)).degree
      (xiForward system coarse steps center) := by
    exact_mod_cast xiSimpleGraph_degree_positive system rule_connected (coarse + steps)
      (xiForward system coarse steps center)
  have voltage_source : voltage (xiForward system coarse steps center) = 1 :=
    boundaryVoltageProfile_source _ (xiSimpleGraph_connected system rule_connected _)
      (xiIncidentStarDomain_complement_nonempty system coarse steps center)
      (xiIncidentStarDomain_center_mem system coarse steps center)
  have weighted_sum :
      ((XiSimpleGraph system (coarse + steps)).degree
          (xiForward system coarse steps center) : ℝ) *
        xiSkeletonReturnProbability system rule_connected coarse steps center center =
      ∑ vertex ∈ (XiSimpleGraph system (coarse + steps)).neighborFinset
          (xiForward system coarse steps center), voltage vertex := by
    rw [xiSkeletonReturnProbability_self_eq_voltage_average system rule_connected rules_loopless
      rules_unique planting_nonadjacent coarse steps center,
      transProb_smul_sum degree_positive voltage]
    exact mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr degree_positive.ne') _
  have capacity := boundaryVoltageProfile_laplacian_source
    (XiSimpleGraph system (coarse + steps)) (xiSimpleGraph_connected system rule_connected _)
    (xiIncidentStarDomain_complement_nonempty system coarse steps center)
    (xiIncidentStarDomain_center_mem system coarse steps center)
  change ((XiSimpleGraph system (coarse + steps)).lapMatrix ℝ *ᵥ voltage)
    (xiForward system coarse steps center) = _ at capacity
  rw [lapMatrix_mulVec_apply, voltage_source, mul_one] at capacity
  rw [← weighted_sum] at capacity
  nlinarith

/-- The actual duration until the next distinct skeleton vertex is
precisely the actual incident-star center exit mean. -/
theorem xiSkeletonDistinctDuration_eq_star_exit (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (center : XiVtx system coarse) :
    xiSkeletonReturnDuration system coarse steps center /
        (1 - xiSkeletonReturnProbability system rule_connected coarse steps center center) =
      expExit (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center) (xiForward system coarse steps center) := by
  have escape_positive := xiSkeletonReturnChain_departure_positive system rule_connected rules_loopless
    rules_unique planting_nonadjacent coarse steps center
  change 0 < 1 - xiSkeletonReturnProbability system rule_connected coarse steps center center
    at escape_positive
  have resistance_positive := effResToBoundary_pos (XiSimpleGraph system (coarse + steps))
    (xiSimpleGraph_connected system rule_connected _)
    (xiIncidentStarDomain_complement_nonempty system coarse steps center)
    (xiIncidentStarDomain_center_mem system coarse steps center)
  have capacity := xiSkeletonReturnProbability_escape_capacity system rule_connected rules_loopless
    rules_unique planting_nonadjacent coarse steps center
  have cancellation :
      effResToBoundary (XiSimpleGraph system (coarse + steps))
          (xiIncidentStarDomain system coarse steps center) (xiForward system coarse steps center) *
        ((XiSimpleGraph system (coarse + steps)).degree
          (xiForward system coarse steps center) : ℝ) *
        (1 - xiSkeletonReturnProbability system rule_connected coarse steps center center) = 1 := by
    rw [mul_assoc, capacity, mul_inv_cancel₀ resistance_positive.ne']
  apply (div_eq_iff escape_positive.ne').mpr
  rw [expExit_eq_resistance_mul_voltage_mass _ (xiSimpleGraph_connected system rule_connected _)
    (xiIncidentStarDomain_complement_nonempty system coarse steps center)
    (xiIncidentStarDomain_center_mem system coarse steps center),
    ← xiSkeletonReturnDuration_mul_degree_eq_voltage_mass system rule_connected rules_loopless
      rules_unique planting_nonadjacent coarse steps center]
  calc
    _ = 1 * xiSkeletonReturnDuration system coarse steps center := by ring
    _ = (effResToBoundary (XiSimpleGraph system (coarse + steps))
          (xiIncidentStarDomain system coarse steps center) (xiForward system coarse steps center) *
        ((XiSimpleGraph system (coarse + steps)).degree
          (xiForward system coarse steps center) : ℝ) *
        (1 - xiSkeletonReturnProbability system rule_connected coarse steps center center)) *
          xiSkeletonReturnDuration system coarse steps center := by rw [cancellation]
    _ = _ := by ring

/-- The genuine accumulated return-excursion cost up to the first distinct
coarse vertex equals the actual star exit mean, under no time-bound input. -/
theorem xiSkeletonReturnChain_distinct_cost_eq_star_exit (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (center : XiVtx system coarse) :
    costLim (xiSkeletonReturnChain system rule_connected coarse steps) (Finset.univ.erase center)
        (xiSkeletonReturnDuration system coarse steps) center =
      expExit (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center) (xiForward system coarse steps center) := by
  rw [costLim_until_distinct (xiSkeletonReturnChain system rule_connected coarse steps)
    (xiSkeletonReturnChain_departure_positive system rule_connected rules_loopless rules_unique
      planting_nonadjacent coarse steps)
    (xiSkeletonReturnDuration system coarse steps)
    (xiSkeletonReturnDuration_nonnegative system coarse steps) center]
  exact xiSkeletonDistinctDuration_eq_star_exit system rule_connected rules_loopless rules_unique
    planting_nonadjacent coarse steps center

/-- The actual distinct-jump time bound required in the paper's cell
recursion follows from the already proved actual star-center bound. -/
theorem xiSkeletonDistinctDuration_spectral_upper (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse steps (center : XiVtx system coarse),
      xiSkeletonReturnDuration system coarse steps center /
          (1 - xiSkeletonReturnProbability system rule_connected coarse steps center center) ≤
        upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rule_connected distance_positive) ^ steps := by
  obtain ⟨upper, positive, bound⟩ := xiIncidentStarDomain_expExit_spectral_upper system rule_connected
    rules_loopless rules_unique planting_nonadjacent distance_positive
  refine ⟨upper, positive, fun coarse steps center => ?_⟩
  rw [xiSkeletonDistinctDuration_eq_star_exit system rule_connected rules_loopless rules_unique
    planting_nonadjacent coarse steps center]
  exact bound coarse steps center

end EIGS

#print axioms EIGS.xiSkeletonHitting_eq_star_voltage
#print axioms EIGS.xiSkeletonReturnProbability_self_eq_voltage_average
#print axioms EIGS.xiSkeletonReturnDuration_eq_excursionTime
#print axioms EIGS.laplacian_pairing_symmetric
#print axioms EIGS.harmonic_mass_eq_degree_mul_return_duration
#print axioms EIGS.xiSkeletonReturnDuration_mul_degree_eq_voltage_mass
#print axioms EIGS.boundaryVoltageProfile_laplacian_source
#print axioms EIGS.xiSkeletonReturnProbability_escape_capacity
#print axioms EIGS.xiSkeletonDistinctDuration_eq_star_exit
#print axioms EIGS.xiSkeletonReturnChain_distinct_cost_eq_star_exit
#print axioms EIGS.xiSkeletonDistinctDuration_spectral_upper
