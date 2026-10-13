import RequestProject.Section31.VaryingBanachOperatorApproximation

/-! Finite observation products with genuine supremum-norm approximation.
This Banach-space recursion imposes no Hilbert structure on continuous
functions or finite vertex functions. Moving starts are evaluated directly,
without averaging against an invariant measure. -/

namespace IGS.Sec31.BanachBackwardObservations

open Filter Topology

variable {Time Test Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def backwardProduct (evolution : Time → Space →L[ℝ] Space)
    (multiplication : Test → Space →L[ℝ] Space) : List (Time × Test) → Space → Space
  | [], terminal => terminal
  | observation :: remaining, terminal => multiplication observation.2
      (evolution observation.1 (backwardProduct evolution multiplication remaining terminal))

theorem backwardProduct_uniform_limit
    {LevelSpace : ℕ → Type*} [∀ level, NormedAddCommGroup (LevelSpace level)]
    [∀ level, NormedSpace ℝ (LevelSpace level)]
    (restriction : ∀ level, Space →L[ℝ] LevelSpace level)
    (levelEvolution : ∀ level, Time → LevelSpace level →L[ℝ] LevelSpace level)
    (evolution : Time → Space →L[ℝ] Space)
    (levelMultiplication : ∀ level, Test → LevelSpace level →L[ℝ] LevelSpace level)
    (multiplication : Test → Space →L[ℝ] Space)
    (evolutionBound : Time → ℝ) (multiplicationBound : Test → ℝ)
    (levelEvolutionBound : ∀ level time, ‖levelEvolution level time‖ ≤ evolutionBound time)
    (levelMultiplicationBound : ∀ level test, ‖levelMultiplication level test‖ ≤ multiplicationBound test)
    (evolutionConvergence : ∀ time values,
      Tendsto (fun level => ‖levelEvolution level time (restriction level values) -
        restriction level (evolution time values)‖) atTop (𝓝 0))
    (multiplicationConvergence : ∀ test values,
      Tendsto (fun level => ‖levelMultiplication level test (restriction level values) -
        restriction level (multiplication test values)‖) atTop (𝓝 0))
    (observations : List (Time × Test)) (terminalSequence : ∀ level, LevelSpace level) (terminal : Space)
    (terminalConvergence : Tendsto (fun level => ‖terminalSequence level - restriction level terminal‖)
      atTop (𝓝 0)) :
    Tendsto (fun level => ‖backwardProduct (levelEvolution level) (levelMultiplication level)
      observations (terminalSequence level) - restriction level
        (backwardProduct evolution multiplication observations terminal)‖) atTop (𝓝 0) := by
  induction observations with
  | nil => exact terminalConvergence
  | cons observation remaining induction =>
      apply VaryingBanachOperatorApproximation.varying_apply restriction
        (fun level => levelMultiplication level observation.2) (multiplication observation.2)
        (multiplicationBound observation.2) (fun level => levelMultiplicationBound level observation.2)
        (multiplicationConvergence observation.2)
      exact VaryingBanachOperatorApproximation.varying_apply restriction
        (fun level => levelEvolution level observation.1) (evolution observation.1)
        (evolutionBound observation.1) (fun level => levelEvolutionBound level observation.1)
        (evolutionConvergence observation.1) _ _ induction

theorem moving_start_evaluation_limit
    {LimitSpace : Type*} [TopologicalSpace LimitSpace]
    {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
    (embedding : ∀ level, Vertex level → LimitSpace)
    (values : ∀ level, Vertex level → ℝ) (function : C(LimitSpace, ℝ))
    (uniformConvergence : Tendsto (fun level => ‖values level -
      fun vertex => function (embedding level vertex)‖) atTop (𝓝 0))
    (starts : ∀ level, Vertex level) (start : LimitSpace)
    (startsConverge : Tendsto (fun level => embedding level (starts level)) atTop (𝓝 start)) :
    Tendsto (fun level => values level (starts level)) atTop (𝓝 (function start)) := by
  have errorLimit : Tendsto (fun level =>
      values level (starts level) - function (embedding level (starts level))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun level => norm_le_pi_norm
        (values level - fun vertex => function (embedding level vertex)) (starts level))
      uniformConvergence
  have evaluationLimit := function.continuous.continuousAt.tendsto.comp startsConverge
  have result := errorLimit.add evaluationLimit
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using result

end IGS.Sec31.BanachBackwardObservations

#print axioms IGS.Sec31.BanachBackwardObservations.backwardProduct_uniform_limit
#print axioms IGS.Sec31.BanachBackwardObservations.moving_start_evaluation_limit
