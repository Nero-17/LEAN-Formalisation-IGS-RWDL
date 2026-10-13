import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Explicit asymptotic relations for genuinely varying real Hilbert spaces.

The data are a dense linear core and restrictions whose norms converge, as in
the common-space restriction construction of Kuwae--Shioya. Strong convergence
means uniform eventual approximation by restrictions of a nearby core element.
Weak convergence tests against every strongly convergent sequence using the
actual inner products. These are definitions, not arbitrary predicate fields.
The concrete compact metric space, measures and L² core remain to be connected.
-/

namespace IGS.Sec31

open Filter Topology

theorem inner_polarization_real {Space : Type*} [NormedAddCommGroup Space]
    [InnerProductSpace ℝ Space] (first second : Space) : inner ℝ first second =
      (‖first + second‖ ^ 2 - ‖first‖ ^ 2 - ‖second‖ ^ 2) / 2 := by
  nlinarith [norm_add_sq_real first second]

variable (Core Hilbert : Type*) [AddCommGroup Core] [Module ℝ Core]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  (LevelHilbert : ℕ → Type*)
  [∀ level, NormedAddCommGroup (LevelHilbert level)]
  [∀ level, InnerProductSpace ℝ (LevelHilbert level)]

structure VaryingHilbertCore where
  embed : Core →ₗ[ℝ] Hilbert
  restrict : ∀ level, Core →ₗ[ℝ] LevelHilbert level
  dense : DenseRange embed
  norm_converges : ∀ element : Core,
    Tendsto (fun level => ‖restrict level element‖) atTop (𝓝 ‖embed element‖)

namespace VaryingHilbertCore

variable {Core Hilbert LevelHilbert}
  (core : VaryingHilbertCore Core Hilbert LevelHilbert)

def Strong (sequence : ∀ level, LevelHilbert level) (limit : Hilbert) : Prop :=
  ∀ tolerance : ℝ, 0 < tolerance → ∃ element : Core,
    ‖core.embed element - limit‖ < tolerance ∧
      ∀ᶠ level in atTop, ‖sequence level - core.restrict level element‖ < tolerance

def Weak (sequence : ∀ level, LevelHilbert level) (limit : Hilbert) : Prop :=
  ∀ (tests : ∀ level, LevelHilbert level) (test : Hilbert), core.Strong tests test →
    Tendsto (fun level => inner ℝ (sequence level) (tests level))
      atTop (𝓝 (inner ℝ limit test))

theorem strong_restrict (element : Core) :
    core.Strong (fun level => core.restrict level element) (core.embed element) := by
  intro tolerance positive
  exact ⟨element, by simpa using positive, Filter.Eventually.of_forall (fun _ => by simpa using positive)⟩

theorem strong_norm_tendsto {sequence : ∀ level, LevelHilbert level} {limit : Hilbert}
    (converges : core.Strong sequence limit) :
    Tendsto (fun level => ‖sequence level‖) atTop (𝓝 ‖limit‖) := by
  apply Metric.tendsto_nhds.2
  intro tolerance tolerance_positive
  obtain ⟨element, core_close, sequence_close⟩ := converges (tolerance / 3) (by positivity)
  have norm_close := Metric.tendsto_nhds.1 (core.norm_converges element)
    (tolerance / 3) (by positivity)
  filter_upwards [sequence_close, norm_close] with level sequence_close norm_close
  have bound : dist ‖sequence level‖ ‖limit‖ ≤
      ‖sequence level - core.restrict level element‖ +
        dist ‖core.restrict level element‖ ‖core.embed element‖ +
          ‖core.embed element - limit‖ := by
    calc
      dist ‖sequence level‖ ‖limit‖ ≤
          dist ‖sequence level‖ ‖core.restrict level element‖ +
            dist ‖core.restrict level element‖ ‖limit‖ := dist_triangle _ _ _
      _ ≤ ‖sequence level - core.restrict level element‖ +
          (dist ‖core.restrict level element‖ ‖core.embed element‖ +
            ‖core.embed element - limit‖) := add_le_add
          (by simpa only [dist_eq_norm] using dist_norm_norm_le (sequence level) (core.restrict level element))
          ((dist_triangle ‖core.restrict level element‖ ‖core.embed element‖ ‖limit‖).trans
            (add_le_add le_rfl
              (by simpa only [dist_eq_norm] using dist_norm_norm_le (core.embed element) limit)))
      _ = _ := by ring
  linarith

theorem strong_add {first second : ∀ level, LevelHilbert level} {firstLimit secondLimit : Hilbert}
    (first_converges : core.Strong first firstLimit)
    (second_converges : core.Strong second secondLimit) :
    core.Strong (fun level => first level + second level) (firstLimit + secondLimit) := by
  intro tolerance positive
  obtain ⟨firstCore, first_close, first_eventually⟩ := first_converges (tolerance / 2) (half_pos positive)
  obtain ⟨secondCore, second_close, second_eventually⟩ := second_converges (tolerance / 2) (half_pos positive)
  refine ⟨firstCore + secondCore, ?_, ?_⟩
  · rw [map_add, add_sub_add_comm]
    exact (norm_add_le _ _).trans_lt (by linarith)
  · filter_upwards [first_eventually, second_eventually] with level first_close second_close
    rw [map_add, add_sub_add_comm]
    exact (norm_add_le _ _).trans_lt (by linarith)

theorem strong_inner_tendsto {first second : ∀ level, LevelHilbert level}
    {firstLimit secondLimit : Hilbert}
    (first_converges : core.Strong first firstLimit)
    (second_converges : core.Strong second secondLimit) :
    Tendsto (fun level => inner ℝ (first level) (second level))
      atTop (𝓝 (inner ℝ firstLimit secondLimit)) := by
  have sum_norm := core.strong_norm_tendsto (core.strong_add first_converges second_converges)
  have first_norm := core.strong_norm_tendsto first_converges
  have second_norm := core.strong_norm_tendsto second_converges
  simp_rw [inner_polarization_real]
  exact
    (((sum_norm.pow 2).sub (first_norm.pow 2)).sub (second_norm.pow 2)).div_const 2

theorem strong_implies_weak {sequence : ∀ level, LevelHilbert level} {limit : Hilbert}
    (converges : core.Strong sequence limit) : core.Weak sequence limit := by
  intro tests test test_converges
  exact core.strong_inner_tendsto converges test_converges

end VaryingHilbertCore
end IGS.Sec31
