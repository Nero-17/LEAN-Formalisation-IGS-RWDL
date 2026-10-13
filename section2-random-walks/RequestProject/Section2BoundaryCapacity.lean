import RequestProject.Section2Resistance

/-! Grounded-set Dirichlet capacity on the actual finite simple graph. -/

namespace EIGS

open scoped BigOperators Classical

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
variable (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]

theorem effResToBoundary_pos (connected : graph.Connected) {inside : Finset Vertex}
    (complement_nonempty : insideᶜ.Nonempty) {source : Vertex} (source_inside : source ∈ inside) :
    0 < effResToBoundary graph inside source := by
  rw [green_diag_eq_resistance graph connected complement_nonempty source_inside]
  exact ((dirichletLap_posDef graph connected complement_nonempty).inv).diag_pos

theorem effResToBoundary_mono_domain (connected : graph.Connected)
    {inside outside : Finset Vertex} (contained : inside ⊆ outside)
    (outside_complement_nonempty : outsideᶜ.Nonempty) {source : Vertex}
    (source_inside : source ∈ inside) :
    effResToBoundary graph inside source ≤ effResToBoundary graph outside source := by
  have inside_complement_nonempty : insideᶜ.Nonempty := by
    obtain ⟨vertex, vertex_outside⟩ := outside_complement_nonempty
    exact ⟨vertex, Finset.mem_compl.mpr (fun vertex_inside =>
      (Finset.mem_compl.mp vertex_outside) (contained vertex_inside))⟩
  have flow := harmonicFlow_isFlow graph connected outside_complement_nonempty (contained source_inside)
  have restricted_flow : IsBoundaryUnitFlow graph inside source (harmonicFlow graph outside source) :=
    ⟨flow.1, fun vertex vertex_inside => flow.2 vertex (contained vertex_inside)⟩
  simpa only [flowEnergy_harmonic] using
    thomson_lower graph connected inside_complement_nonempty source_inside restricted_flow

theorem dirichletEnergy_smul (scale : ℝ) (values : Vertex → ℝ) :
    dirichletEnergy graph (fun vertex => scale * values vertex) =
      scale ^ 2 * dirichletEnergy graph values := by
  unfold dirichletEnergy
  have pointwise : ∀ source sink : Vertex,
      (if graph.Adj source sink then (scale * values source - scale * values sink) ^ 2 else 0) =
        scale ^ 2 * (if graph.Adj source sink then (values source - values sink) ^ 2 else 0) := by
    intro source sink
    split_ifs <;> ring
  simp_rw [pointwise, ← Finset.mul_sum]
  ring

noncomputable def boundaryVoltageProfile (inside : Finset Vertex) (source : Vertex) : Vertex → ℝ :=
  fun vertex => (effResToBoundary graph inside source)⁻¹ * unitPotential graph inside source vertex

theorem boundaryVoltageProfile_source (connected : graph.Connected) {inside : Finset Vertex}
    (complement_nonempty : insideᶜ.Nonempty) {source : Vertex} (source_inside : source ∈ inside) :
    boundaryVoltageProfile graph inside source source = 1 := by
  unfold boundaryVoltageProfile
  rw [unitPotential_apply_mem graph source_inside source_inside,
    ← green_diag_eq_resistance graph connected complement_nonempty source_inside]
  exact inv_mul_cancel₀ (ne_of_gt (effResToBoundary_pos graph connected complement_nonempty source_inside))

theorem boundaryVoltageProfile_zero {inside : Finset Vertex} {source vertex : Vertex}
    (vertex_outside : vertex ∉ inside) : boundaryVoltageProfile graph inside source vertex = 0 := by
  simp [boundaryVoltageProfile, unitPotential, vertex_outside]

theorem boundaryVoltageProfile_energy (connected : graph.Connected) {inside : Finset Vertex}
    (complement_nonempty : insideᶜ.Nonempty) {source : Vertex} (source_inside : source ∈ inside) :
    dirichletEnergy graph (boundaryVoltageProfile graph inside source) =
      (effResToBoundary graph inside source)⁻¹ := by
  change dirichletEnergy graph (fun vertex => (effResToBoundary graph inside source)⁻¹ *
    unitPotential graph inside source vertex) = _
  rw [dirichletEnergy_smul]
  change (effResToBoundary graph inside source)⁻¹ ^ 2 * effResToBoundary graph inside source = _
  field_simp [ne_of_gt (effResToBoundary_pos graph connected complement_nonempty source_inside)]

theorem boundaryVoltageProfile_minimum (connected : graph.Connected) {inside : Finset Vertex}
    (complement_nonempty : insideᶜ.Nonempty) {source : Vertex} (source_inside : source ∈ inside)
    (competitor : Vertex → ℝ) (competitor_source : competitor source = 1)
    (competitor_zero : ∀ vertex, vertex ∉ inside → competitor vertex = 0) :
    dirichletEnergy graph (boundaryVoltageProfile graph inside source) ≤
      dirichletEnergy graph competitor := by
  let difference := fun vertex => competitor vertex - boundaryVoltageProfile graph inside source vertex
  have difference_zero : ∀ vertex, vertex ∉ inside.erase source → difference vertex = 0 := by
    intro vertex vertex_outside
    by_cases vertex_inside : vertex ∈ inside
    · have same_source : vertex = source := by simpa only [Finset.mem_erase, vertex_inside, and_true, not_not] using vertex_outside
      subst vertex
      simp only [difference, competitor_source,
        boundaryVoltageProfile_source graph connected complement_nonempty source_inside, sub_self]
    · simp only [difference, competitor_zero vertex vertex_inside,
        boundaryVoltageProfile_zero graph vertex_inside, sub_self]
  have orthogonal := grad_orthogonal graph difference_zero
    (harmonicFlow_antisym graph inside source) (fun vertex vertex_inside => by
      have divergence := (harmonicFlow_isFlow graph connected complement_nonempty source_inside).2
        vertex (Finset.mem_of_mem_erase vertex_inside)
      simpa only [if_neg (Finset.ne_of_mem_erase vertex_inside)] using divergence)
  have voltage_difference : ∀ first second,
      boundaryVoltageProfile graph inside source first - boundaryVoltageProfile graph inside source second =
        (effResToBoundary graph inside source)⁻¹ *
          (unitPotential graph inside source first - unitPotential graph inside source second) := by
    intro first second
    unfold boundaryVoltageProfile
    ring
  have mixed_zero : (∑ first, ∑ second, if graph.Adj first second then
      (difference first - difference second) *
        (boundaryVoltageProfile graph inside source first - boundaryVoltageProfile graph inside source second) else 0) = 0 := by
    have scaled := congrArg (fun value : ℝ => (effResToBoundary graph inside source)⁻¹ * value) orthogonal
    simp only [harmonicFlow] at scaled
    simp_rw [voltage_difference]
    simpa only [Finset.mul_sum, mul_ite, mul_zero, mul_assoc, mul_left_comm, mul_comm] using scaled
  have pointwise : ∀ first second : Vertex,
      (if graph.Adj first second then (competitor first - competitor second) ^ 2 else 0) =
        (if graph.Adj first second then (difference first - difference second) ^ 2 else 0) +
        (if graph.Adj first second then
          (boundaryVoltageProfile graph inside source first - boundaryVoltageProfile graph inside source second) ^ 2 else 0) +
        2 * (if graph.Adj first second then (difference first - difference second) *
          (boundaryVoltageProfile graph inside source first - boundaryVoltageProfile graph inside source second) else 0) := by
    intro first second
    by_cases adjacent : graph.Adj first second
    · simp only [if_pos adjacent]
      dsimp only [difference]
      ring
    · simp only [if_neg adjacent]
      norm_num
  have energy_decomposition : dirichletEnergy graph competitor = dirichletEnergy graph difference +
      dirichletEnergy graph (boundaryVoltageProfile graph inside source) := by
    unfold dirichletEnergy
    simp_rw [pointwise, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [mixed_zero]
    ring
  have difference_nonnegative : 0 ≤ dirichletEnergy graph difference :=
    flowEnergy_nonneg graph (fun first second => difference first - difference second)
  linarith

theorem effResToBoundary_eq_inverse_minimum_energy (connected : graph.Connected)
    {inside : Finset Vertex} (complement_nonempty : insideᶜ.Nonempty)
    {source : Vertex} (source_inside : source ∈ inside) (minimizer : Vertex → ℝ)
    (minimizer_source : minimizer source = 1)
    (minimizer_zero : ∀ vertex, vertex ∉ inside → minimizer vertex = 0)
    (minimum : ∀ competitor : Vertex → ℝ, competitor source = 1 →
      (∀ vertex, vertex ∉ inside → competitor vertex = 0) →
      dirichletEnergy graph minimizer ≤ dirichletEnergy graph competitor) :
    effResToBoundary graph inside source = (dirichletEnergy graph minimizer)⁻¹ := by
  have minimum_value : dirichletEnergy graph minimizer =
      dirichletEnergy graph (boundaryVoltageProfile graph inside source) := by
    exact le_antisymm
      (minimum _ (boundaryVoltageProfile_source graph connected complement_nonempty source_inside)
        (fun _ vertex_outside => boundaryVoltageProfile_zero graph vertex_outside))
      (boundaryVoltageProfile_minimum graph connected complement_nonempty source_inside
        minimizer minimizer_source minimizer_zero)
  rw [minimum_value, boundaryVoltageProfile_energy graph connected complement_nonempty source_inside, inv_inv]

end EIGS

#print axioms EIGS.effResToBoundary_pos
#print axioms EIGS.effResToBoundary_mono_domain
#print axioms EIGS.dirichletEnergy_smul
#print axioms EIGS.boundaryVoltageProfile_source
#print axioms EIGS.boundaryVoltageProfile_zero
#print axioms EIGS.boundaryVoltageProfile_energy
#print axioms EIGS.boundaryVoltageProfile_minimum
#print axioms EIGS.effResToBoundary_eq_inverse_minimum_energy
