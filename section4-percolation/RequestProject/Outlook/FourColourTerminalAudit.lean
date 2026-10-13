import RequestProject.Outlook.CorrectedMatrices
import RequestProject.Cluster.InfiniteProcess

/-! Terminal exchange audit. The matrix calculation concerns the literal directed
figure. The percolation calculation concerns the existing Bernoulli configuration
law conditioned on connection. No identification of these two models is assumed. -/
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

namespace Outlook
open Matrix Reduced MeasureTheory
open scoped BigOperators

theorem correctedCriticalEN_square_terminal_difference :
    (correctedCriticalEN ^ 2) 0 0 - (correctedCriticalEN ^ 2) 1 1 = 4 * pc ^ 7 := by
  rw [pow_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_eight]
  change ((4*pc^2)*(4*pc^2) + 0*0 + (2*pc^4)*(2*pc^2) + 0*0 +
      (2*pc^5)*(2*pc^2) + 0*0 + 0*0 + 0*0) -
    (0*0 + (4*pc^2)*(4*pc^2) + 0*0 + (2*pc^4)*(2*pc^2) +
      0*0 + (2*pc^5)*0 + 0*0 + 0*0) = 4*pc^7
  ring

theorem correctedCriticalEN_square_terminal_asymmetric :
    (correctedCriticalEN ^ 2) 1 1 < (correctedCriticalEN ^ 2) 0 0 := by
  have positive : 0 < 4 * pc ^ 7 := mul_pos (by norm_num) (pow_pos pc_pos 7)
  linarith [correctedCriticalEN_square_terminal_difference]
end Outlook

namespace Cluster
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Reflection through the vertical axis of the actual recursive diamond. -/
def reverseConfiguration : (n : ℕ) → Conf n → Conf n
  | 0 => id
  | n + 1 => fun configuration =>
      (reverseConfiguration n configuration.2.1, reverseConfiguration n configuration.1,
       reverseConfiguration n configuration.2.2.2, reverseConfiguration n configuration.2.2.1)

theorem reverseConfiguration_involutive (n : ℕ) : Function.Involutive (reverseConfiguration n) := by
  induction n with
  | zero => intro configuration; rfl
  | succ n inductionHypothesis =>
    rintro ⟨first, second, third, fourth⟩
    have inner (configuration : Conf n) := inductionHypothesis configuration
    simp only [reverseConfiguration, inner]

def reverseConfigurationEquiv (n : ℕ) : Conf n ≃ Conf n :=
  Function.Involutive.toPerm (reverseConfiguration n) (reverseConfiguration_involutive n)

theorem conn_reverseConfiguration (n : ℕ) (configuration : Conf n) :
    conn n (reverseConfiguration n configuration) = conn n configuration := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
    simp only [reverseConfiguration, conn_succ, inductionHypothesis, Bool.and_comm]

/-- Number of finest open edges incident to the left terminal. -/
def leftOpenIncidences : (n : ℕ) → Conf n → ℕ
  | 0 => fun configuration : Bool => if configuration then 1 else 0
  | n + 1 => fun configuration =>
      leftOpenIncidences n configuration.1 + leftOpenIncidences n configuration.2.2.1

/-- Number of finest open edges incident to the right terminal. -/
def rightOpenIncidences : (n : ℕ) → Conf n → ℕ
  | 0 => fun configuration : Bool => if configuration then 1 else 0
  | n + 1 => fun configuration =>
      rightOpenIncidences n configuration.2.1 + rightOpenIncidences n configuration.2.2.2

theorem leftOpenIncidences_reverse (n : ℕ) (configuration : Conf n) :
    leftOpenIncidences n (reverseConfiguration n configuration) = rightOpenIncidences n configuration := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
    simp only [reverseConfiguration, leftOpenIncidences, rightOpenIncidences, inductionHypothesis]

/-- Actual oriented incidence counts in the already constructed open network. -/
def TTN.sourceTailCount (network : TTN) : ℕ :=
  ∑ edge, if network.tail edge = network.a then 1 else 0

def TTN.sinkHeadCount (network : TTN) : ℕ :=
  ∑ edge, if network.head edge = network.b then 1 else 0

theorem TTN.sourceTailCount_series (first second : TTN) :
    (TTN.seriesTTN first second).sourceTailCount = first.sourceTailCount := by
  unfold TTN.sourceTailCount
  change (∑ edge : first.E ⊕ second.E, if (TTN.seriesTTN first second).tail edge =
      (TTN.seriesTTN first second).a then 1 else 0) = _
  rw [Fintype.sum_sum_type]
  simp [TTN.seriesTTN, TTN.seriesEmb_eq_inl, Ne.symm first.hab]

theorem TTN.sinkHeadCount_series (first second : TTN) :
    (TTN.seriesTTN first second).sinkHeadCount = second.sinkHeadCount := by
  unfold TTN.sinkHeadCount
  change (∑ edge : first.E ⊕ second.E, if (TTN.seriesTTN first second).head edge =
      (TTN.seriesTTN first second).b then 1 else 0) = _
  rw [Fintype.sum_sum_type]
  simp only [TTN.seriesTTN, Sum.elim_inl, Sum.elim_inr,
    TTN.seriesEmb, dif_neg (Ne.symm second.hab), Sum.inl_ne_inr, ite_false,
    Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases atSource : second.head edge = second.a
  · simp [atSource, second.hab]
  · simp [atSource, Subtype.ext_iff]

theorem TTN.sourceTailCount_par (first second : TTN) :
    (TTN.parTTN first second).sourceTailCount = first.sourceTailCount + second.sourceTailCount := by
  unfold TTN.sourceTailCount
  change (∑ edge : first.E ⊕ second.E, if (TTN.parTTN first second).tail edge =
      (TTN.parTTN first second).a then 1 else 0) = _
  rw [Fintype.sum_sum_type]
  simp [TTN.parTTN, TTN.parEmb_eq_inl, Ne.symm first.hab]

theorem TTN.sinkHeadCount_par (first second : TTN) :
    (TTN.parTTN first second).sinkHeadCount = first.sinkHeadCount + second.sinkHeadCount := by
  unfold TTN.sinkHeadCount
  change (∑ edge : first.E ⊕ second.E, if (TTN.parTTN first second).head edge =
      (TTN.parTTN first second).b then 1 else 0) = _
  rw [Fintype.sum_sum_type]
  simp [TTN.parTTN, TTN.parEmb_eq_inl, first.hab]

theorem leftOpenIncidences_eq_net (n : ℕ) (configuration : Conf n) :
    leftOpenIncidences n configuration = (net n configuration).sourceTailCount := by
  induction n with
  | zero =>
    cases configuration <;>
      simp [leftOpenIncidences, net, TTN.sourceTailCount, TTN.edgeTTN, TTN.gapTTN]
  | succ n inductionHypothesis =>
    simp only [leftOpenIncidences, net, TTN.sourceTailCount_par,
      TTN.sourceTailCount_series, inductionHypothesis]

theorem rightOpenIncidences_eq_net (n : ℕ) (configuration : Conf n) :
    rightOpenIncidences n configuration = (net n configuration).sinkHeadCount := by
  induction n with
  | zero =>
    cases configuration <;>
      simp [rightOpenIncidences, net, TTN.sinkHeadCount, TTN.edgeTTN, TTN.gapTTN]
  | succ n inductionHypothesis =>
    simp only [rightOpenIncidences, net, TTN.sinkHeadCount_par,
      TTN.sinkHeadCount_series, inductionHypothesis]

private theorem configuration_product_singleton (p : ℝ) (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (n : ℕ) (configuration : Conf (n+1)) :
    confMeasure p (n+1) {configuration} =
      confMeasure p n {configuration.1} * (confMeasure p n {configuration.2.1} *
        (confMeasure p n {configuration.2.2.1} * confMeasure p n {configuration.2.2.2})) := by
  haveI := isProb_confMeasure nonnegative atMostOne n
  rcases configuration with ⟨first, second, third, fourth⟩
  change ((confMeasure p n).prod ((confMeasure p n).prod ((confMeasure p n).prod
    (confMeasure p n)))) {(first, second, third, fourth)} = _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    ← Set.singleton_prod_singleton, Measure.prod_prod]

theorem confMeasure_reverse_singleton (p : ℝ) (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1)
    (n : ℕ) (configuration : Conf n) :
    confMeasure p n {reverseConfiguration n configuration} = confMeasure p n {configuration} := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
    rw [configuration_product_singleton p nonnegative atMostOne,
      configuration_product_singleton p nonnegative atMostOne]
    simp only [reverseConfiguration, inductionHypothesis]
    ring

theorem connectedMeasure_reverse_singleton (n : ℕ) (configuration : Conf n) :
    connectedMeasure n {reverseConfiguration n configuration} = connectedMeasure n {configuration} := by
  have intersection (value : Conf n) : connSet n ∩ {value} =
      if conn n value = true then {value} else ∅ := by
    ext candidate
    simp only [connSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    by_cases equal : candidate=value
    · subst candidate; split_ifs <;> simp_all
    · split_ifs <;> simp_all
  rw [connectedMeasure, ProbabilityTheory.cond_apply (measurableSet_connSet n),
    ProbabilityTheory.cond_apply (measurableSet_connSet n), intersection, intersection,
    conn_reverseConfiguration]
  split_ifs
  · rw [confMeasure_reverse_singleton _ Reduced.pc_pos.le Reduced.pc_lt_one.le]
  · rfl

theorem connected_terminal_incidence_expectations_equal (n : ℕ) :
    (∫ configuration, (leftOpenIncidences n configuration : ℝ) ∂connectedMeasure n) =
    ∫ configuration, (rightOpenIncidences n configuration : ℝ) ∂connectedMeasure n := by
  rw [integral_fintype _ Integrable.of_finite, integral_fintype _ Integrable.of_finite]
  simp only [measureReal_def]
  calc
    _ = ∑ configuration, (connectedMeasure n {reverseConfiguration n configuration}).toReal •
        (leftOpenIncidences n (reverseConfiguration n configuration) : ℝ) :=
      (Equiv.sum_comp (reverseConfigurationEquiv n)
        (fun configuration => (connectedMeasure n {configuration}).toReal •
          (leftOpenIncidences n configuration : ℝ))).symm
    _ = _ := by simp only [connectedMeasure_reverse_singleton, leftOpenIncidences_reverse]

theorem connected_actual_terminal_expectations_equal (n : ℕ) :
    (∫ configuration, ((net n configuration).sourceTailCount : ℝ) ∂connectedMeasure n) =
    ∫ configuration, ((net n configuration).sinkHeadCount : ℝ) ∂connectedMeasure n := by
  simp_rw [← leftOpenIncidences_eq_net, ← rightOpenIncidences_eq_net]
  exact connected_terminal_incidence_expectations_equal n
end Cluster

#print axioms Outlook.correctedCriticalEN_square_terminal_difference
#print axioms Outlook.correctedCriticalEN_square_terminal_asymmetric
#print axioms Cluster.reverseConfiguration_involutive
#print axioms Cluster.conn_reverseConfiguration
#print axioms Cluster.leftOpenIncidences_reverse
#print axioms Cluster.confMeasure_reverse_singleton
#print axioms Cluster.connectedMeasure_reverse_singleton
#print axioms Cluster.connected_terminal_incidence_expectations_equal

#print axioms Cluster.leftOpenIncidences_eq_net
#print axioms Cluster.rightOpenIncidences_eq_net
#print axioms Cluster.connected_actual_terminal_expectations_equal
