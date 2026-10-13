import RequestProject.Section31.HarmonicProfileContinuity
import RequestProject.Section31.AffineProfileExtension

/-! Constructed finite harmonic extensions for an arbitrary nonempty finite
boundary. Existence, range bounds and continuity are derived from connectivity
and the actual edge sums, rather than assumed for coarse harmonic splines. -/

namespace EIGS.Network

open IGS.Sec31 Filter Topology

variable {K : ℕ} (network : Network K)

theorem exists_boundary_potential_minimum
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (boundary : Finset network.V) (boundaryNonempty : boundary.Nonempty)
    (boundaryValues : network.V → ℝ) :
    ∃ potential : network.V → ℝ,
      (∀ vertex ∈ boundary, potential vertex = boundaryValues vertex) ∧
      ∀ competitor : network.V → ℝ,
        (∀ vertex ∈ boundary, competitor vertex = boundaryValues vertex) →
        (network.potentialNetwork resistances positive).energy potential ≤
          (network.potentialNetwork resistances positive).energy competitor := by
  have boundaryNonemptyCopy := boundaryNonempty
  obtain ⟨anchor, anchorMembership⟩ := boundaryNonemptyCopy
  obtain ⟨poincareConstant, poincareNonnegative, poincareBound⟩ :=
    network.exists_potential_poincare_constant resistances positive anchor connected
  exact (network.potentialNetwork resistances positive).exists_min boundary boundaryValues
    poincareConstant poincareNonnegative (fun perturbation perturbationBoundary vertex =>
      poincareBound perturbation (perturbationBoundary anchor anchorMembership) vertex)

noncomputable def boundaryPotentialProfile
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (boundary : Finset network.V) (boundaryNonempty : boundary.Nonempty)
    (boundaryValues : network.V → ℝ) : network.V → ℝ :=
  Classical.choose (network.exists_boundary_potential_minimum resistances positive connected
    boundary boundaryNonempty boundaryValues)

theorem boundaryPotentialProfile_boundary
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (boundary : Finset network.V) (boundaryNonempty : boundary.Nonempty)
    (boundaryValues : network.V → ℝ) (vertex : network.V) (membership : vertex ∈ boundary) :
    network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues vertex =
      boundaryValues vertex :=
  (Classical.choose_spec (network.exists_boundary_potential_minimum resistances positive connected
    boundary boundaryNonempty boundaryValues)).1 vertex membership

theorem boundaryPotentialProfile_minimal
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (boundary : Finset network.V) (boundaryNonempty : boundary.Nonempty)
    (boundaryValues competitor : network.V → ℝ)
    (competitorBoundary : ∀ vertex ∈ boundary, competitor vertex = boundaryValues vertex) :
    (network.potentialNetwork resistances positive).energy
        (network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues) ≤
      (network.potentialNetwork resistances positive).energy competitor :=
  (Classical.choose_spec (network.exists_boundary_potential_minimum resistances positive connected
    boundary boundaryNonempty boundaryValues)).2 competitor competitorBoundary

theorem boundaryPotentialProfile_range
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (boundary : Finset network.V) (boundaryNonempty : boundary.Nonempty)
    (boundaryValues : network.V → ℝ)
    (boundaryRange : ∀ vertex ∈ boundary, 0 ≤ boundaryValues vertex ∧ boundaryValues vertex ≤ 1) :
    ∀ vertex, 0 ≤ network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues vertex ∧
      network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues vertex ≤ 1 := by
  have boundaryNonemptyCopy := boundaryNonempty
  obtain ⟨anchor, anchorMembership⟩ := boundaryNonemptyCopy
  obtain ⟨poincareConstant, poincareNonnegative, poincareBound⟩ :=
    network.exists_potential_poincare_constant resistances positive anchor connected
  exact (network.potentialNetwork resistances positive).range_subset_of_min boundary boundaryValues
    poincareConstant (fun perturbation perturbationBoundary vertex =>
      poincareBound perturbation (perturbationBoundary anchor anchorMembership) vertex)
    boundaryRange _
    (network.boundaryPotentialProfile_boundary resistances positive connected boundary boundaryNonempty boundaryValues)
    (network.boundaryPotentialProfile_minimal resistances positive connected boundary boundaryNonempty boundaryValues)

theorem boundaryPotentialProfile_affine
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (boundary : Finset network.V) (boundaryNonempty : boundary.Nonempty)
    (boundaryValues : network.V → ℝ) (constant scalar : ℝ) :
    network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty
        (fun vertex => constant + scalar * boundaryValues vertex) =
      (fun vertex => constant + scalar *
        network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues vertex) := by
  apply network.potential_minimum_unique resistances positive connected boundary boundaryNonempty
    (fun vertex => constant + scalar * boundaryValues vertex)
  · exact network.boundaryPotentialProfile_boundary resistances positive connected boundary boundaryNonempty _
  · intro vertex membership
    rw [network.boundaryPotentialProfile_boundary resistances positive connected boundary boundaryNonempty
      boundaryValues vertex membership]
  · exact network.boundaryPotentialProfile_minimal resistances positive connected boundary boundaryNonempty _
  · exact (network.potentialNetwork resistances positive).min_affine boundary boundaryValues
      (network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues)
      constant scalar
      (network.boundaryPotentialProfile_minimal resistances positive connected boundary boundaryNonempty boundaryValues)

theorem exists_boundary_potential_stability_bound
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (boundary : Finset network.V) (boundaryNonempty : boundary.Nonempty)
    (boundaryValues : network.V → ℝ)
    (boundaryRange : ∀ vertex ∈ boundary, 0 ≤ boundaryValues vertex ∧ boundaryValues vertex ≤ 1) :
    ∃ stabilityConstant : ℝ, 0 ≤ stabilityConstant ∧
      ∀ (newResistances : Fin K → ℝ) (newPositive : ∀ colour, 0 < newResistances colour) (vertex : network.V),
        (network.boundaryPotentialProfile newResistances newPositive connected boundary boundaryNonempty boundaryValues vertex -
          network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues vertex) ^ 2 ≤
        stabilityConstant * ∑ edge, |(newResistances (network.color edge))⁻¹ - (resistances (network.color edge))⁻¹| := by
  have boundaryNonemptyCopy := boundaryNonempty
  obtain ⟨anchor, anchorMembership⟩ := boundaryNonemptyCopy
  obtain ⟨poincareConstant, poincareNonnegative, poincareBound⟩ :=
    network.exists_potential_poincare_constant resistances positive anchor connected
  refine ⟨2 * poincareConstant, mul_nonneg (by norm_num) poincareNonnegative, ?_⟩
  intro newResistances newPositive vertex
  have firstRange := network.boundaryPotentialProfile_range resistances positive connected boundary boundaryNonempty
    boundaryValues boundaryRange
  have secondRange := network.boundaryPotentialProfile_range newResistances newPositive connected boundary boundaryNonempty
    boundaryValues boundaryRange
  have firstError := network.potential_energy_change_le_conductance_difference resistances newResistances positive newPositive
    (network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues) firstRange
  have secondError := network.potential_energy_change_le_conductance_difference resistances newResistances positive newPositive
    (network.boundaryPotentialProfile newResistances newPositive connected boundary boundaryNonempty boundaryValues) secondRange
  have pythagoras := (network.potentialNetwork resistances positive).energy_sub_of_min (↑boundary : Set network.V)
    boundaryValues
    (network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues)
    (network.boundaryPotentialProfile_boundary resistances positive connected boundary boundaryNonempty boundaryValues)
    (network.boundaryPotentialProfile_minimal resistances positive connected boundary boundaryNonempty boundaryValues)
    (network.boundaryPotentialProfile newResistances newPositive connected boundary boundaryNonempty boundaryValues)
    (network.boundaryPotentialProfile_boundary newResistances newPositive connected boundary boundaryNonempty boundaryValues)
  have newComparison := network.boundaryPotentialProfile_minimal newResistances newPositive connected boundary boundaryNonempty
    boundaryValues (network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues)
    (network.boundaryPotentialProfile_boundary resistances positive connected boundary boundaryNonempty boundaryValues)
  have residualEnergy : (network.potentialNetwork resistances positive).energy
      (network.boundaryPotentialProfile newResistances newPositive connected boundary boundaryNonempty boundaryValues -
        network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues) ≤
      2 * ∑ edge, |(newResistances (network.color edge))⁻¹ - (resistances (network.color edge))⁻¹| := by
    linarith [(abs_le.1 firstError).2, (abs_le.1 secondError).1]
  have anchorZero :
      (network.boundaryPotentialProfile newResistances newPositive connected boundary boundaryNonempty boundaryValues -
        network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues) anchor = 0 := by
    simp only [Pi.sub_apply, network.boundaryPotentialProfile_boundary _ _ connected boundary boundaryNonempty
      boundaryValues anchor anchorMembership, sub_self]
  have pointBound := poincareBound _ anchorZero vertex
  have scaledResidual := mul_le_mul_of_nonneg_left residualEnergy poincareNonnegative
  dsimp only [Pi.sub_apply] at pointBound
  nlinarith

theorem boundaryPotentialProfile_tendsto_of_unit_boundary
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (resistanceSequence : ℕ → Fin K → ℝ) (sequencePositive : ∀ index colour, 0 < resistanceSequence index colour)
    (resistancesConverge : ∀ colour,
      Tendsto (fun index => resistanceSequence index colour) atTop (𝓝 (resistances colour)))
    (connected : network.toSimpleGraph.Connected)
    (boundary : Finset network.V) (boundaryNonempty : boundary.Nonempty)
    (boundaryValues : network.V → ℝ)
    (boundaryRange : ∀ vertex ∈ boundary, 0 ≤ boundaryValues vertex ∧ boundaryValues vertex ≤ 1)
    (vertex : network.V) :
    Tendsto (fun index => network.boundaryPotentialProfile (resistanceSequence index) (sequencePositive index)
        connected boundary boundaryNonempty boundaryValues vertex) atTop
      (𝓝 (network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues vertex)) := by
  obtain ⟨stabilityConstant, stabilityNonnegative, stabilityBound⟩ :=
    network.exists_boundary_potential_stability_bound resistances positive connected boundary boundaryNonempty
      boundaryValues boundaryRange
  have coordinateDifferenceLimit : ∀ edge : network.E, Tendsto (fun index =>
      |(resistanceSequence index (network.color edge))⁻¹ - (resistances (network.color edge))⁻¹|) atTop (𝓝 0) := by
    intro edge
    have constantLimit : Tendsto (fun _ : ℕ => (resistances (network.color edge))⁻¹) atTop
        (𝓝 ((resistances (network.color edge))⁻¹)) := tendsto_const_nhds
    simpa only [sub_self, abs_zero] using
      (((resistancesConverge (network.color edge)).inv₀ (ne_of_gt (positive _))).sub constantLimit).abs
  have conductanceDifferenceLimit : Tendsto (fun index =>
      ∑ edge, |(resistanceSequence index (network.color edge))⁻¹ - (resistances (network.color edge))⁻¹|) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun edge _ => coordinateDifferenceLimit edge)
  have rootLimit : Tendsto (fun index => Real.sqrt (stabilityConstant *
      ∑ edge, |(resistanceSequence index (network.color edge))⁻¹ - (resistances (network.color edge))⁻¹|)) atTop (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (conductanceDifferenceLimit.const_mul stabilityConstant)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [Real.norm_eq_abs] using squeeze_zero (fun _ => abs_nonneg _)
    (fun index => Real.abs_le_sqrt (stabilityBound (resistanceSequence index) (sequencePositive index) vertex)) rootLimit

theorem boundaryPotentialProfile_tendsto
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (resistanceSequence : ℕ → Fin K → ℝ) (sequencePositive : ∀ index colour, 0 < resistanceSequence index colour)
    (resistancesConverge : ∀ colour,
      Tendsto (fun index => resistanceSequence index colour) atTop (𝓝 (resistances colour)))
    (connected : network.toSimpleGraph.Connected)
    (boundary : Finset network.V) (boundaryNonempty : boundary.Nonempty)
    (boundaryValues : network.V → ℝ) (vertex : network.V) :
    Tendsto (fun index => network.boundaryPotentialProfile (resistanceSequence index) (sequencePositive index)
        connected boundary boundaryNonempty boundaryValues vertex) atTop
      (𝓝 (network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues vertex)) := by
  let boundaryBound : ℝ := ‖boundaryValues‖ + 1
  have boundPositive : 0 < boundaryBound := by dsimp [boundaryBound]; positivity
  have inverseNonnegative : 0 ≤ (2 * boundaryBound)⁻¹ := inv_nonneg.2 (by positivity)
  have inverseHalf : (2 * boundaryBound)⁻¹ * boundaryBound = 1 / 2 := by
    field_simp [boundPositive.ne']
  have normalizedBoundaryRange : ∀ boundaryVertex ∈ boundary,
      0 ≤ 1 / 2 + (2 * boundaryBound)⁻¹ * boundaryValues boundaryVertex ∧
        1 / 2 + (2 * boundaryBound)⁻¹ * boundaryValues boundaryVertex ≤ 1 := by
    intro boundaryVertex membership
    have absoluteBound : |boundaryValues boundaryVertex| ≤ boundaryBound := by
      calc
        _ = ‖boundaryValues boundaryVertex‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖boundaryValues‖ := norm_le_pi_norm boundaryValues boundaryVertex
        _ ≤ boundaryBound := by dsimp [boundaryBound]; linarith
    have lowerBound := mul_le_mul_of_nonneg_left (abs_le.1 absoluteBound).1 inverseNonnegative
    have upperBound := mul_le_mul_of_nonneg_left (abs_le.1 absoluteBound).2 inverseNonnegative
    constructor <;> nlinarith
  have normalizedConvergence := network.boundaryPotentialProfile_tendsto_of_unit_boundary resistances positive
    resistanceSequence sequencePositive resistancesConverge connected boundary boundaryNonempty
      (fun boundaryVertex => 1 / 2 + (2 * boundaryBound)⁻¹ * boundaryValues boundaryVertex)
      normalizedBoundaryRange vertex
  have denormalization (newResistances : Fin K → ℝ) (newPositive : ∀ colour, 0 < newResistances colour) :
      2 * boundaryBound * network.boundaryPotentialProfile newResistances newPositive connected boundary boundaryNonempty
        (fun boundaryVertex => 1 / 2 + (2 * boundaryBound)⁻¹ * boundaryValues boundaryVertex) vertex - boundaryBound =
      network.boundaryPotentialProfile newResistances newPositive connected boundary boundaryNonempty boundaryValues vertex := by
    rw [network.boundaryPotentialProfile_affine newResistances newPositive connected boundary boundaryNonempty
      boundaryValues (1 / 2) ((2 * boundaryBound)⁻¹)]
    field_simp [boundPositive.ne']
    ring
  simpa only [denormalization] using (normalizedConvergence.const_mul (2 * boundaryBound)).sub_const boundaryBound

theorem boundaryPotentialProfile_norm_sub_tendsto_zero
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (resistanceSequence : ℕ → Fin K → ℝ) (sequencePositive : ∀ index colour, 0 < resistanceSequence index colour)
    (resistancesConverge : ∀ colour,
      Tendsto (fun index => resistanceSequence index colour) atTop (𝓝 (resistances colour)))
    (connected : network.toSimpleGraph.Connected)
    (boundary : Finset network.V) (boundaryNonempty : boundary.Nonempty)
    (boundaryValues : network.V → ℝ) :
    Tendsto (fun index => ‖network.boundaryPotentialProfile (resistanceSequence index) (sequencePositive index)
        connected boundary boundaryNonempty boundaryValues -
      network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues‖)
      atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.1
  apply tendsto_pi_nhds.2
  exact network.boundaryPotentialProfile_tendsto resistances positive resistanceSequence sequencePositive
    resistancesConverge connected boundary boundaryNonempty boundaryValues

end EIGS.Network
