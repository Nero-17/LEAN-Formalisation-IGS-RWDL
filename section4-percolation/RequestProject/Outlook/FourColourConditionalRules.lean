import RequestProject.Outlook.FourColourRuleAudit
import RequestProject.Cluster.Coarse

/-! The figure probabilities as conditional probabilities of the actual four
independent Bernoulli cells. For green, the active terminal is the source.
This one-step statement does not identify the iterated literal coding with the
unoriented critical percolation cluster. -/
namespace Outlook.FourColourRuleAudit
open MeasureTheory ProbabilityTheory Cluster
open scoped BigOperators ENNReal Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
local instance : DecidableEq (Conf 0) := inferInstanceAs (DecidableEq Bool)

/-- The conditioning event for the figure: connected for red, disconnected
for blue and green, and unrestricted for the bookkeeping black rule. -/
def conditioningEvent (parent : Fin 4) : Set (Conf 1) :=
  {configuration | if parent=0 then conn 1 configuration=true
    else if parent=3 then True else conn 1 configuration=false}

def connectedOutcome : Conf 1 → Fin 9
  | (true,true,true,true) => 0
  | (true,false,true,true) => 1
  | (false,true,true,true) => 2
  | (true,true,true,false) => 3
  | (true,true,false,true) => 4
  | (true,true,false,false) => 5
  | (false,false,true,true) => 6
  | _ => 0

def disconnectedOutcome : Conf 1 → Fin 9
  | (true,false,false,false) => 0
  | (false,true,false,false) => 1
  | (false,false,true,false) => 2
  | (false,false,false,true) => 3
  | (true,false,true,false) => 4
  | (false,true,false,true) => 5
  | (true,false,false,true) => 6
  | (false,true,true,false) => 7
  | (false,false,false,false) => 8
  | _ => 0

def activeSourceOutcome (configuration : Conf 1) : Fin 9 :=
  if configuration.1 = true then (if configuration.2.2.1 = true then 2 else 0)
  else (if configuration.2.2.1 = true then 1 else 3)

def conditionedOutcome (parent : Fin 4) (configuration : Conf 1) : Fin 9 :=
  if parent=0 then connectedOutcome configuration
  else if parent=1 then disconnectedOutcome configuration
  else if parent=2 then activeSourceOutcome configuration else 0

noncomputable def configurationWeight (p : ℝ) (configuration : Conf 1) : ℝ :=
  (if configuration.1 = true then p else 1-p) *
  ((if configuration.2.1 = true then p else 1-p) *
  ((if configuration.2.2.1 = true then p else 1-p) * (if configuration.2.2.2 = true then p else 1-p)))

theorem configurationWeight_eq_actual (p : ℝ) (nonnegative : 0≤p) (atMostOne : p≤1)
    (configuration : Conf 1) :
    configurationWeight p configuration = (confMeasure p 1).real {configuration} := by
  haveI := Cluster.isProb_bern nonnegative atMostOne
  rcases configuration with ⟨first, second, third, fourth⟩
  change _ = (((bern p).prod ((bern p).prod ((bern p).prod (bern p))))
    {(first,second,third,fourth)}).toReal
  rw [← Set.singleton_prod_singleton, Measure.prod_prod,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    ← Set.singleton_prod_singleton, Measure.prod_prod]
  cases first <;> cases second <;> cases third <;> cases fourth <;>
    simp [configurationWeight, bern, ENNReal.toReal_mul, nonnegative,
      sub_nonneg.mpr atMostOne]

private theorem measureReal_eq_finite_sum (p : ℝ) (nonnegative : 0≤p) (atMostOne : p≤1)
    (event : Set (Conf 1)) :
    (confMeasure p 1).real event =
      ∑ configuration, if configuration ∈ event then configurationWeight p configuration else 0 := by
  classical
  haveI := Cluster.isProb_confMeasure nonnegative atMostOne 1
  simp_rw [configurationWeight_eq_actual p nonnegative atMostOne]
  rw [← Finset.sum_filter]
  simpa using (sum_measureReal_singleton (μ := confMeasure p 1)
    (s := Finset.univ.filter (fun configuration => configuration∈event))).symm

noncomputable def conditioningMass (p : ℝ) (parent : Fin 4) : ℝ :=
  if parent=0 then 2*p^2-p^4 else if parent=3 then 1 else (1-p)^2*(1+p)^2

private theorem sum_conf_one (test : Conf 1 → ℝ) :
    (∑ configuration, test configuration) =
      ∑ first : Bool, ∑ second : Bool, ∑ third : Bool, ∑ fourth : Bool,
        test (first,second,third,fourth) := by
  change (∑ configuration : Bool × Bool × Bool × Bool, test configuration) = _
  simp only [Fintype.sum_prod_type]

theorem conditioningMass_eq_sum (p : ℝ) (parent : Fin 4) :
    conditioningMass p parent = ∑ configuration,
      if configuration ∈ conditioningEvent parent then configurationWeight p configuration else 0 := by
  classical
  rw [sum_conf_one]
  fin_cases parent <;>
    simp [conditioningMass, conditioningEvent, configurationWeight, conn,
      Fintype.sum_bool] <;> ring

theorem conditional_figure_probabilities (p : ℝ) (nonnegative : 0≤p) (atMostOne : p≤1)
    (parent : Fin 4) (outcome : Fin 9) :
    (ProbabilityTheory.cond (confMeasure p 1) (conditioningEvent parent)).real
        {configuration | conditionedOutcome parent configuration=outcome} =
      figureWeights p parent outcome := by
  classical
  rw [measureReal_def, ProbabilityTheory.cond_apply (MeasurableSet.of_discrete),
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((confMeasure p 1).real (conditioningEvent parent))⁻¹ *
    (confMeasure p 1).real (conditioningEvent parent ∩
      {configuration | conditionedOutcome parent configuration=outcome}) = _
  rw [measureReal_eq_finite_sum p nonnegative atMostOne,
    ← conditioningMass_eq_sum, measureReal_eq_finite_sum p nonnegative atMostOne]
  rw [sum_conf_one]
  fin_cases parent <;> fin_cases outcome <;>
    simp [conditioningMass, conditioningEvent, configurationWeight, conditionedOutcome,
      connectedOutcome, disconnectedOutcome, activeSourceOutcome, conn, figureWeights,
      Fintype.sum_bool, div_eq_mul_inv] <;> ring
theorem critical_conditional_figure_probabilities (parent : Fin 4) (outcome : Fin 9) :
    (ProbabilityTheory.cond (confMeasure Reduced.pc 1) (conditioningEvent parent)).real
        {configuration | conditionedOutcome parent configuration=outcome} =
      criticalWeights parent outcome := by
  rw [conditional_figure_probabilities Reduced.pc Reduced.pc_pos.le Reduced.pc_lt_one.le]
  exact congrFun (congrFun figureWeights_critical parent) outcome

end Outlook.FourColourRuleAudit

#print axioms Outlook.FourColourRuleAudit.configurationWeight_eq_actual
#print axioms Outlook.FourColourRuleAudit.conditioningMass_eq_sum
#print axioms Outlook.FourColourRuleAudit.conditional_figure_probabilities
#print axioms Outlook.FourColourRuleAudit.critical_conditional_figure_probabilities
