import RequestProject.Section31.EIGSNativeDiscreteEnergy
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Exact native speed-L² quadrature over the actual edges. Counting endpoints
instead of closed cells keeps shared boundary degrees explicit. -/

namespace EIGS

open MeasureTheory
open scoped BigOperators ENNReal

variable {K : ℕ}

theorem xiVertexSpeedMeasure_integral_endpoints (system : EIGSData K)
    (mass : XiMassParameters system) (level : ℕ) (values : XiVtx system level → ℝ) :
    (∫ vertex, values vertex ∂xiVertexSpeedMeasure system mass level) =
      (∫ edge, values (XiTail system level edge) + values (XiHead system level edge)
        ∂mass.uniformEdgeMeasure level) / 2 := by
  have tailIntegrable : Integrable values
      ((mass.uniformEdgeMeasure level).map (XiTail system level)) := Integrable.of_finite
  have headIntegrable : Integrable values
      ((mass.uniformEdgeMeasure level).map (XiHead system level)) := Integrable.of_finite
  rw [xiVertexSpeedMeasure, integral_add_measure
    (tailIntegrable.smul_measure (ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num)))
    (headIntegrable.smul_measure (ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num)))]
  simp only [integral_smul_measure, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat, smul_eq_mul]
  rw [integral_map Measurable.of_discrete.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
    integral_map Measurable.of_discrete.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
    integral_add Integrable.of_finite Integrable.of_finite]
  ring

theorem xiUniformEdgeMeasure_integral_sum (system : EIGSData K)
    (mass : XiMassParameters system) (level : ℕ)
    (values : XiEdge system.toRuleData level → ℝ) :
    (∫ edge, values edge ∂mass.uniformEdgeMeasure level) =
      (∑ edge, values edge) / totalEdges system.toRuleData level := by
  classical
  letI : Nonempty (XiEdge system.toRuleData level) := mass.edge_nonempty level
  change (∫ edge, values edge ∂(PMF.uniformOfFintype (XiEdge system.toRuleData level)).toMeasure) = _
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, totalEdges, div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

theorem xiFiniteSpeedL2_norm_sq_integral (system : EIGSData K)
    (mass : XiMassParameters system) (level : ℕ) (values : XiVtx system level → ℝ) :
    ‖xiFiniteSpeedL2 system mass level values‖ ^ 2 =
      ∫ vertex, (values vertex) ^ 2 ∂xiVertexSpeedMeasure system mass level := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [xiFiniteSpeedL2_ae system mass level values] with vertex equality
  rw [equality]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem xiFiniteSpeedL2_norm_sq_endpoints (system : EIGSData K)
    (mass : XiMassParameters system) (level : ℕ) (values : XiVtx system level → ℝ) :
    ‖xiFiniteSpeedL2 system mass level values‖ ^ 2 =
      (∑ edge : XiEdge system.toRuleData level,
        ((values (XiTail system level edge)) ^ 2 + (values (XiHead system level edge)) ^ 2)) /
        (2 * totalEdges system.toRuleData level) := by
  rw [xiFiniteSpeedL2_norm_sq_integral, xiVertexSpeedMeasure_integral_endpoints,
    xiUniformEdgeMeasure_integral_sum]
  ring

end EIGS
