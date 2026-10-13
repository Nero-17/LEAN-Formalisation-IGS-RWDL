import RequestProject.Outlook.CorrectedMatrices
import RequestProject.Section1
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Complete finite enumeration of the original figure's four-colour rules.
There are seven red, nine blue and four green outcomes; unused entries have
zero weight. Black remains the explicit cemetery placeholder used in the paper.
The expected matrices count only live offspring and live boundary incidences. -/

namespace Outlook.FourColourRuleAudit

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

set_option maxHeartbeats 2000000

local instance : MeasurableSpace (Fin 9) := ⊤
local instance : DiscreteMeasurableSpace (Fin 9) := ⟨fun _ => trivial⟩

def source : Fin 4 → Fin 4 := GreenRuleAudit.source
def target : Fin 4 → Fin 4 := GreenRuleAudit.target

def colour : Fin 4 → (Fin 9) → Fin 4 → Fin 4 :=
  ![![![0,0,0,0], ![0,1,0,0], ![1,0,0,0], ![0,0,0,1], ![0,0,1,0],
      ![0,0,2,2], ![2,2,0,0], ![3,3,3,3], ![3,3,3,3]],
    ![![0,1,2,2], ![1,0,2,2], ![2,2,0,1], ![2,2,1,0], ![0,1,0,1],
      ![1,0,1,0], ![0,1,1,0], ![1,0,0,1], ![2,2,2,2]],
    ![![0,2,2,3], ![2,3,0,2], ![0,2,0,2], ![2,3,2,3], ![3,3,3,3],
      ![3,3,3,3], ![3,3,3,3], ![3,3,3,3], ![3,3,3,3]],
    ![![3,3,3,3], ![3,3,3,3], ![3,3,3,3], ![3,3,3,3], ![3,3,3,3],
      ![3,3,3,3], ![3,3,3,3], ![3,3,3,3], ![3,3,3,3]]]

def ruleGraph (parent : Fin 4) (outcome : Fin 9) : EIGS.ColGraph 4 where
  V := Fin 4
  E := Fin 4
  tail := source
  head := target
  col := colour parent outcome

def ruleSystem (outcomeSelection : Fin 4 → Fin 9) : EIGS.EIGSData 4 where
  initCol := 0
  rule := fun parent => ruleGraph parent (outcomeSelection parent)
  plantPlus := fun _ => (0 : Fin 4)
  plantMinus := fun _ => (2 : Fin 4)
  plant_ne := by intro parent; change (0 : Fin 4) ≠ 2; decide

theorem green_outcomes_eq_original (outcome : Fin 4) :
    colour 2 ⟨outcome.val, by omega⟩ = GreenRuleAudit.colour outcome := by
  fin_cases outcome <;> rfl
def totalCount (parent : Fin 4) (outcome : (Fin 9)) (selected : Fin 4) : ℕ :=
  (Outlook.colourEdges Finset.univ (colour parent outcome) selected).card

def outgoingCount (parent : Fin 4) (outcome : (Fin 9)) (selected : Fin 4) : ℕ :=
  (Outlook.boundaryColourEdges Finset.univ source (colour parent outcome) 0 selected).card

def incomingCount (parent : Fin 4) (outcome : (Fin 9)) (selected : Fin 4) : ℕ :=
  (Outlook.boundaryColourEdges Finset.univ target (colour parent outcome) 2 selected).card

def totalCountTable : Fin 4 → (Fin 9) → Fin 4 → ℕ :=
  ![![![4,0,0,0], ![3,1,0,0], ![3,1,0,0], ![3,1,0,0], ![3,1,0,0],
      ![2,0,2,0], ![2,0,2,0], ![0,0,0,4], ![0,0,0,4]],
    ![![1,1,2,0], ![1,1,2,0], ![1,1,2,0], ![1,1,2,0], ![2,2,0,0],
      ![2,2,0,0], ![2,2,0,0], ![2,2,0,0], ![0,0,4,0]],
    ![![1,0,2,1], ![1,0,2,1], ![2,0,2,0], ![0,0,2,2], ![0,0,0,4],
      ![0,0,0,4], ![0,0,0,4], ![0,0,0,4], ![0,0,0,4]],
    ![![0,0,0,4], ![0,0,0,4], ![0,0,0,4], ![0,0,0,4], ![0,0,0,4],
      ![0,0,0,4], ![0,0,0,4], ![0,0,0,4], ![0,0,0,4]]]

def outgoingCountTable : Fin 4 → (Fin 9) → Fin 4 → ℕ :=
  ![![![2,0,0,0], ![2,0,0,0], ![1,1,0,0], ![2,0,0,0], ![1,1,0,0],
      ![1,0,1,0], ![1,0,1,0], ![0,0,0,2], ![0,0,0,2]],
    ![![1,0,1,0], ![0,1,1,0], ![1,0,1,0], ![0,1,1,0], ![2,0,0,0],
      ![0,2,0,0], ![1,1,0,0], ![1,1,0,0], ![0,0,2,0]],
    ![![1,0,1,0], ![1,0,1,0], ![2,0,0,0], ![0,0,2,0], ![0,0,0,2],
      ![0,0,0,2], ![0,0,0,2], ![0,0,0,2], ![0,0,0,2]],
    ![![0,0,0,2], ![0,0,0,2], ![0,0,0,2], ![0,0,0,2], ![0,0,0,2],
      ![0,0,0,2], ![0,0,0,2], ![0,0,0,2], ![0,0,0,2]]]

def incomingCountTable : Fin 4 → (Fin 9) → Fin 4 → ℕ :=
  ![![![2,0,0,0], ![1,1,0,0], ![2,0,0,0], ![1,1,0,0], ![2,0,0,0],
      ![1,0,1,0], ![1,0,1,0], ![0,0,0,2], ![0,0,0,2]],
    ![![0,1,1,0], ![1,0,1,0], ![0,1,1,0], ![1,0,1,0], ![0,2,0,0],
      ![2,0,0,0], ![1,1,0,0], ![1,1,0,0], ![0,0,2,0]],
    ![![0,0,1,1], ![0,0,1,1], ![0,0,2,0], ![0,0,0,2], ![0,0,0,2],
      ![0,0,0,2], ![0,0,0,2], ![0,0,0,2], ![0,0,0,2]],
    ![![0,0,0,2], ![0,0,0,2], ![0,0,0,2], ![0,0,0,2], ![0,0,0,2],
      ![0,0,0,2], ![0,0,0,2], ![0,0,0,2], ![0,0,0,2]]]

theorem totalCount_eq_table : totalCount = totalCountTable := by decide
theorem outgoingCount_eq_table : outgoingCount = outgoingCountTable := by decide
theorem incomingCount_eq_table : incomingCount = incomingCountTable := by decide

noncomputable def criticalWeights : Fin 4 → (Fin 9) → ℝ :=
  ![![Reduced.pc^3, Reduced.pc^4, Reduced.pc^4, Reduced.pc^4, Reduced.pc^4,
      Reduced.pc^5, Reduced.pc^5, 0, 0],
    ![Reduced.pc^5, Reduced.pc^5, Reduced.pc^5, Reduced.pc^5, Reduced.pc^4,
      Reduced.pc^4, Reduced.pc^4, Reduced.pc^4, Reduced.pc^6],
    ![Reduced.pc^3, Reduced.pc^3, Reduced.pc^4, Reduced.pc^2, 0,0,0,0,0],
    ![(1:ℝ),0,0,0,0,0,0,0,0]]

noncomputable def figureWeights (p : ℝ) : Fin 4 → Fin 9 → ℝ :=
  ![![p^4/(2*p^2-p^4), p^3*(1-p)/(2*p^2-p^4), p^3*(1-p)/(2*p^2-p^4),
      p^3*(1-p)/(2*p^2-p^4), p^3*(1-p)/(2*p^2-p^4),
      p^2*(1-p)^2/(2*p^2-p^4), p^2*(1-p)^2/(2*p^2-p^4), 0,0],
    ![p*(1-p)^3/((1-p)^2*(1+p)^2), p*(1-p)^3/((1-p)^2*(1+p)^2),
      p*(1-p)^3/((1-p)^2*(1+p)^2), p*(1-p)^3/((1-p)^2*(1+p)^2),
      p^2*(1-p)^2/((1-p)^2*(1+p)^2), p^2*(1-p)^2/((1-p)^2*(1+p)^2),
      p^2*(1-p)^2/((1-p)^2*(1+p)^2), p^2*(1-p)^2/((1-p)^2*(1+p)^2),
      (1-p)^4/((1-p)^2*(1+p)^2)],
    ![p*(1-p)^2/((1-p)^2*(1+p)^2), p*(1-p)^2/((1-p)^2*(1+p)^2),
      p^2*(1-p)^2/((1-p)^2*(1+p)^2), (1-p)^2/((1-p)^2*(1+p)^2), 0,0,0,0,0],
    ![(1:ℝ),0,0,0,0,0,0,0,0]]
private theorem critical_power_three : Reduced.pc^3 = 2*Reduced.pc-1 := by
  rw [pow_succ, Reduced.pc_sq]
  nlinarith [Reduced.pc_sq]

private theorem critical_power_four : Reduced.pc^4 = 2-3*Reduced.pc := by
  rw [show (4:ℕ)=3+1 by rfl, pow_succ, critical_power_three]
  nlinarith [Reduced.pc_sq]

private theorem critical_power_five : Reduced.pc^5 = 5*Reduced.pc-3 := by
  rw [show (5:ℕ)=4+1 by rfl, pow_succ, critical_power_four]
  nlinarith [Reduced.pc_sq]

private theorem critical_power_six : Reduced.pc^6 = 5-8*Reduced.pc := by
  calc
    Reduced.pc^6 = Reduced.pc^5 * Reduced.pc := by ring
    _ = 5-8*Reduced.pc := by rw [critical_power_five]; nlinarith [Reduced.pc_sq]

theorem figureWeights_critical : figureWeights Reduced.pc = criticalWeights := by
  have redDenominator : 2*Reduced.pc^2-Reduced.pc^4=Reduced.pc := by
    rw [critical_power_four, Reduced.pc_sq]
    ring
  have disconnectedDenominator : (1-Reduced.pc)^2*(1+Reduced.pc)^2=Reduced.pc^2 := by
    calc
      _ = (1-Reduced.pc^2)^2 := by ring
      _ = Reduced.pc^2 := by congr 1; linarith [Reduced.pc_sq]
  ext parent outcome
  fin_cases parent <;> fin_cases outcome <;>
    dsimp only [figureWeights, criticalWeights, Matrix.vecCons, Fin.cons] <;>
    simp only [redDenominator, disconnectedDenominator]
  all_goals try simp only [← Reduced.pc_sq]
  all_goals field_simp [Reduced.pc_pos.ne']
  all_goals ring
theorem criticalWeights_nonnegative (parent : Fin 4) (outcome : (Fin 9)) :
    0 ≤ criticalWeights parent outcome := by
  fin_cases parent <;> fin_cases outcome <;>
    first | exact pow_nonneg Reduced.pc_pos.le _ | exact le_rfl | exact zero_le_one

theorem criticalWeights_sum_one (parent : Fin 4) : ∑ outcome, criticalWeights parent outcome = 1 := by
  fin_cases parent <;> norm_num [criticalWeights, Fin.sum_univ_succ]
  all_goals simp only [critical_power_six, critical_power_five, critical_power_four,
    critical_power_three, Reduced.pc_sq]
  all_goals ring

noncomputable def outcomePMF (parent : Fin 4) : PMF (Fin 9) :=
  PMF.ofFintype (fun outcome => ENNReal.ofReal (criticalWeights parent outcome)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun outcome _ => criticalWeights_nonnegative parent outcome),
      criticalWeights_sum_one]
    norm_num)

noncomputable def expected (parent : Fin 4) (counts : (Fin 9) → ℕ) : ℝ :=
  ∑ outcome, criticalWeights parent outcome * (counts outcome : ℝ)

noncomputable def meanLiveMass : Matrix (Fin 4) (Fin 4) ℝ := fun parent selected =>
  if parent=3 ∨ selected=3 then 0 else expected parent (fun outcome => totalCount parent outcome selected)

def boundaryParent (state : Fin 8) : Fin 4 := ⟨state.val/2, by omega⟩

noncomputable def meanLiveBoundary : Matrix (Fin 8) (Fin 8) ℝ := fun row column =>
  if boundaryParent row=3 ∨ boundaryParent column=3 ∨ row.val%2 ≠ column.val%2 then 0
  else expected (boundaryParent row) (fun outcome =>
    if row.val%2=0 then outgoingCount (boundaryParent row) outcome (boundaryParent column)
    else incomingCount (boundaryParent row) outcome (boundaryParent column))

theorem meanLiveMass_eq_EM : meanLiveMass = Outlook.EM Reduced.pc := by
  ext parent selected
  rw [meanLiveMass]
  simp_rw [totalCount_eq_table]
  fin_cases parent <;> fin_cases selected <;>
    norm_num [expected, criticalWeights, totalCountTable, Outlook.EM, Fin.sum_univ_succ, Fin.ext_iff]
  all_goals simp only [critical_power_six, critical_power_five, critical_power_four,
    critical_power_three, Reduced.pc_sq]
  all_goals ring

theorem meanLiveBoundary_eq_correctedCriticalEN : meanLiveBoundary = Outlook.correctedCriticalEN := by
  ext row column
  rw [meanLiveBoundary]
  simp_rw [outgoingCount_eq_table, incomingCount_eq_table]
  fin_cases row <;> fin_cases column <;>
    norm_num [boundaryParent, expected, criticalWeights, outgoingCountTable, incomingCountTable,
      Outlook.correctedCriticalEN, Outlook.EN, Fin.sum_univ_succ, Fin.ext_iff]
  all_goals simp only [critical_power_six, critical_power_five, critical_power_four,
    critical_power_three, Reduced.pc_sq]
  all_goals ring

theorem expected_eq_actual_integral (parent : Fin 4) (counts : (Fin 9) → ℕ) :
    expected parent counts = ∫ outcome, (counts outcome : ℝ) ∂(outcomePMF parent).toMeasure := by
  have singleton (outcome : Fin 9) : (outcomePMF parent).toMeasure {outcome} =
      outcomePMF parent outcome := (outcomePMF parent).toMeasure_apply_singleton outcome MeasurableSet.of_discrete
  rw [integral_fintype _ Integrable.of_finite]
  simp only [measureReal_def, singleton]
  simp only [outcomePMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (criticalWeights_nonnegative parent _), smul_eq_mul, expected]

end Outlook.FourColourRuleAudit

#print axioms Outlook.FourColourRuleAudit.ruleSystem
#print axioms Outlook.FourColourRuleAudit.green_outcomes_eq_original
#print axioms Outlook.FourColourRuleAudit.totalCount_eq_table
#print axioms Outlook.FourColourRuleAudit.outgoingCount_eq_table
#print axioms Outlook.FourColourRuleAudit.incomingCount_eq_table
#print axioms Outlook.FourColourRuleAudit.figureWeights_critical
#print axioms Outlook.FourColourRuleAudit.criticalWeights_sum_one
#print axioms Outlook.FourColourRuleAudit.outcomePMF
#print axioms Outlook.FourColourRuleAudit.meanLiveMass_eq_EM
#print axioms Outlook.FourColourRuleAudit.meanLiveBoundary_eq_correctedCriticalEN
#print axioms Outlook.FourColourRuleAudit.expected_eq_actual_integral