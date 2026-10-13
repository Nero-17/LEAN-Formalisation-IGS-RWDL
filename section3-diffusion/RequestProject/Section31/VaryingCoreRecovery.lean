import RequestProject.Section31.VaryingStrongRecovery
import RequestProject.Section31.VaryingL2Approximation
import RequestProject.Section31.CoreRecovery

/-! # Joint state and energy recovery from a genuine varying-Hilbert core

The state convergence is the explicit Kuwae--Shioya `Strong` relation.
Only fixed core elements have recovery rows as an input. A strongly convergent
reference sequence and a diagonal of its distances to those rows produce one
state-and-energy recovery at every original discretization index. The energy
values may lie in any pseudometric space; no energy continuity is assumed.

The concrete EIGS common metric realization, speed-measure convergence,
joint core density and fixed harmonic-core recovery remain separate inputs.
-/

namespace IGS.Sec31

open Filter Topology

namespace VaryingHilbertCore

variable {Core Hilbert : Type*} [AddCommGroup Core] [Module ℝ Core]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  {LevelHilbert : ℕ → Type*}
  [∀ level, NormedAddCommGroup (LevelHilbert level)]
  [∀ level, InnerProductSpace ℝ (LevelHilbert level)]

theorem strong_sub (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    {first second : ∀ level, LevelHilbert level} {first_limit second_limit : Hilbert}
    (first_converges : core.Strong first first_limit)
    (second_converges : core.Strong second second_limit) :
    core.Strong (fun level => first level - second level) (first_limit - second_limit) := by
  intro tolerance tolerance_positive
  obtain ⟨first_element, first_close, first_eventually⟩ :=
    first_converges (tolerance / 2) (half_pos tolerance_positive)
  obtain ⟨second_element, second_close, second_eventually⟩ :=
    second_converges (tolerance / 2) (half_pos tolerance_positive)
  refine ⟨first_element - second_element, ?_, ?_⟩
  · rw [map_sub, sub_sub_sub_comm]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  · filter_upwards [first_eventually, second_eventually]
      with level first_close second_close
    rw [map_sub, sub_sub_sub_comm]
    exact (norm_sub_le _ _).trans_lt (by linarith)

theorem strong_norm_sub_tendsto (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    {first second : ∀ level, LevelHilbert level} {first_limit second_limit : Hilbert}
    (first_converges : core.Strong first first_limit)
    (second_converges : core.Strong second second_limit) :
    Tendsto (fun level => ‖first level - second level‖)
      atTop (𝓝 ‖first_limit - second_limit‖) :=
  core.strong_norm_tendsto (core.strong_sub first_converges second_converges)

variable {Energy : Type*} [PseudoMetricSpace Energy]

/-- The row selection varies; its discretization argument remains the original level. -/
theorem exists_diagonal_state_energy_recovery
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (level_energy : ∀ level, LevelHilbert level → Energy)
    (limit_energy : Hilbert → Energy) (target : Hilbert)
    (approximants : ℕ → Core) (rows : ℕ → ∀ level, LevelHilbert level)
    (state_convergence : Tendsto (fun depth => core.embed (approximants depth))
      atTop (𝓝 target))
    (energy_convergence : Tendsto (fun depth => limit_energy (core.embed (approximants depth)))
      atTop (𝓝 (limit_energy target)))
    (row_state_convergence : ∀ depth, core.Strong (rows depth) (core.embed (approximants depth)))
    (row_energy_convergence : ∀ depth,
      Tendsto (fun level => level_energy level (rows depth level))
        atTop (𝓝 (limit_energy (core.embed (approximants depth))))) :
    ∃ selection : ℕ → ℕ, Tendsto selection atTop atTop ∧
      core.Strong (fun level => rows (selection level) level) target ∧
      Tendsto (fun level => level_energy level (rows (selection level) level))
        atTop (𝓝 (limit_energy target)) := by
  obtain ⟨reference, reference_converges⟩ := core.exists_strong_recovery target
  have limiting_distances : Tendsto
      (fun depth => ‖core.embed (approximants depth) - target‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (state_convergence.sub (tendsto_const_nhds (x := target))).norm
  obtain ⟨selection, selection_tendsto, joint_convergence⟩ := exists_diagonal_tendsto
    (fun depth => (‖core.embed (approximants depth) - target‖,
      limit_energy (core.embed (approximants depth))))
    (fun depth level => (‖rows depth level - reference level‖,
      level_energy level (rows depth level)))
    (0, limit_energy target) (limiting_distances.prodMk_nhds energy_convergence)
    (fun depth => (core.strong_norm_sub_tendsto
      (row_state_convergence depth) reference_converges).prodMk_nhds
        (row_energy_convergence depth))
  refine ⟨selection, selection_tendsto, ?_, ?_⟩
  · apply core.strong_of_norm_sub_tendsto_zero
      (fun level => rows (selection level) level) reference target reference_converges
    exact (continuous_fst.tendsto _).comp joint_convergence
  · exact (continuous_snd.tendsto _).comp joint_convergence

/-- Fixed-core recovery and joint target approximation suffice for full-index recovery. -/
theorem exists_state_energy_recovery_of_core
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (level_energy : ∀ level, LevelHilbert level → Energy)
    (limit_energy : Hilbert → Energy) (target : Hilbert)
    (approximants : ℕ → Core)
    (state_convergence : Tendsto (fun depth => core.embed (approximants depth))
      atTop (𝓝 target))
    (energy_convergence : Tendsto (fun depth => limit_energy (core.embed (approximants depth)))
      atTop (𝓝 (limit_energy target)))
    (core_recovery : ∀ element : Core, ∃ row : ∀ level, LevelHilbert level,
      core.Strong row (core.embed element) ∧
        Tendsto (fun level => level_energy level (row level))
          atTop (𝓝 (limit_energy (core.embed element)))) :
    ∃ sequence : ∀ level, LevelHilbert level,
      core.Strong sequence target ∧
        Tendsto (fun level => level_energy level (sequence level))
          atTop (𝓝 (limit_energy target)) := by
  classical
  choose rows row_state_convergence row_energy_convergence using
    fun depth => core_recovery (approximants depth)
  obtain ⟨selection, _, state_recovery, energy_recovery⟩ :=
    core.exists_diagonal_state_energy_recovery level_energy limit_energy target
      approximants rows state_convergence energy_convergence
      row_state_convergence row_energy_convergence
  exact ⟨fun level => rows (selection level) level, state_recovery, energy_recovery⟩

/-- Joint core density extends recovery to every target without assuming that conclusion. -/
theorem exists_state_energy_recovery_of_joint_core_density
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (level_energy : ∀ level, LevelHilbert level → Energy)
    (limit_energy : Hilbert → Energy)
    (joint_core_density : ∀ target : Hilbert, ∃ approximants : ℕ → Core,
      Tendsto (fun depth => core.embed (approximants depth)) atTop (𝓝 target) ∧
        Tendsto (fun depth => limit_energy (core.embed (approximants depth)))
          atTop (𝓝 (limit_energy target)))
    (core_recovery : ∀ element : Core, ∃ row : ∀ level, LevelHilbert level,
      core.Strong row (core.embed element) ∧
        Tendsto (fun level => level_energy level (row level))
          atTop (𝓝 (limit_energy (core.embed element))))
    (target : Hilbert) :
    ∃ sequence : ∀ level, LevelHilbert level,
      core.Strong sequence target ∧
        Tendsto (fun level => level_energy level (sequence level))
          atTop (𝓝 (limit_energy target)) := by
  obtain ⟨approximants, state_convergence, energy_convergence⟩ := joint_core_density target
  exact core.exists_state_energy_recovery_of_core level_energy limit_energy target
    approximants state_convergence energy_convergence core_recovery

end VaryingHilbertCore
end IGS.Sec31
