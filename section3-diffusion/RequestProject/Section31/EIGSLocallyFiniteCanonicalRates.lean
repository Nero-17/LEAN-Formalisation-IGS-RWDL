import RequestProject.Section31.EIGSLocallyFiniteRuleResistance
import RequestProject.Section2ConcreteSpectralRadius
import RequestProject.Section2ResistanceSpectralRadius
import RequestProject.Section2SpectralRadius

/-! Spectral parameters computed on the two literal locally finite rules.
The weighted-distance lower bound uses the height potential, and the
upper bound uses an actual terminal walk. -/

namespace EIGS
noncomputable section
open scoped Classical BigOperators
set_option maxHeartbeats 2200000

def locallyFiniteRuleDistance (canonical : Bool) : ℝ :=
  if canonical then 3 else 4

def locallyFiniteTerminalWalk (canonical : Bool) :
    ((locallyFiniteRuleSystem canonical).ruleNetwork 0).EdgeWalk (0 : Fin 6) (5 : Fin 6) := by
  cases canonical
  · exact Network.EdgeWalk.cons (0 : Fin 6) (next := (1 : Fin 6)) (by left; constructor <;> rfl)
      (Network.EdgeWalk.cons (1 : Fin 6) (next := (2 : Fin 6)) (by left; constructor <;> rfl)
        (Network.EdgeWalk.cons (2 : Fin 6) (next := (4 : Fin 6)) (by left; constructor <;> rfl)
          (Network.EdgeWalk.cons (5 : Fin 6) (next := (5 : Fin 6)) (by left; constructor <;> rfl)
            (Network.EdgeWalk.nil (network := (locallyFiniteRuleSystem false).ruleNetwork 0) (5 : Fin 6)))))
  · exact Network.EdgeWalk.cons (0 : Fin 6) (next := (1 : Fin 6)) (by left; constructor <;> rfl)
      (Network.EdgeWalk.cons (1 : Fin 6) (next := (4 : Fin 6)) (by left; constructor <;> rfl)
        (Network.EdgeWalk.cons (2 : Fin 6) (next := (5 : Fin 6)) (by left; constructor <;> rfl)
          (Network.EdgeWalk.nil (network := (locallyFiniteRuleSystem true).ruleNetwork 0) (5 : Fin 6))))

theorem locallyFiniteTerminalWalk_cost (canonical : Bool) (lengths : Fin 1 → ℝ) :
    (locallyFiniteTerminalWalk canonical).cost lengths = locallyFiniteRuleDistance canonical * lengths 0 := by
  cases canonical <;>
    simp [locallyFiniteTerminalWalk, Network.EdgeWalk.cost, locallyFiniteRuleDistance,
      EIGSData.ruleNetwork, locallyFiniteRuleSystem, locallyFiniteRuleGraph] <;> ring

def locallyFiniteMetricHeight (canonical : Bool) (vertex : Fin 6) : ℝ :=
  if canonical then
    match vertex.val with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => 2
    | _ => 3
  else
    match vertex.val with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 2
    | 4 => 3
    | _ => 4

theorem locallyFiniteMetricHeight_edge (canonical : Bool) (edge : Fin 6) :
    |locallyFiniteMetricHeight canonical ((locallyFiniteRuleGraph canonical).tail edge) -
      locallyFiniteMetricHeight canonical ((locallyFiniteRuleGraph canonical).head edge)| = 1 := by
  cases canonical <;> fin_cases edge <;>
    norm_num [locallyFiniteMetricHeight, locallyFiniteRuleGraph, Matrix.cons_val_succ]

theorem locallyFiniteMetricPotential_lipschitz (canonical : Bool)
    (lengths : Fin 1 → ℝ) (nonnegative : 0 ≤ lengths) :
    ((locallyFiniteRuleSystem canonical).ruleNetwork 0).EdgeLipschitz lengths
      (fun vertex => lengths 0 * locallyFiniteMetricHeight canonical vertex) := by
  intro edge
  change |lengths 0 * locallyFiniteMetricHeight canonical ((locallyFiniteRuleGraph canonical).tail edge) -
    lengths 0 * locallyFiniteMetricHeight canonical ((locallyFiniteRuleGraph canonical).head edge)| ≤ lengths 0
  rw [← mul_sub, abs_mul, locallyFiniteMetricHeight_edge, abs_of_nonneg (nonnegative 0), mul_one]

theorem locallyFiniteRuleSystem_metricLengths (canonical : Bool)
    (lengths : Fin 1 → ℝ) (nonnegative : 0 ≤ lengths) :
    ((locallyFiniteRuleSystem canonical).ruleFamily
      (locallyFiniteRuleSystem_connected canonical)).metricLengths lengths =
        fun _ => locallyFiniteRuleDistance canonical * lengths 0 := by
  funext colour
  have colourZero : colour = 0 := Subsingleton.elim _ _
  subst colour
  change ((locallyFiniteRuleSystem canonical).ruleNetwork 0).weightedDistance lengths
    (0 : Fin 6) (5 : Fin 6) = locallyFiniteRuleDistance canonical * lengths 0
  apply le_antisymm
  · have bound := ((locallyFiniteRuleSystem canonical).ruleNetwork 0).weightedDistance_le_cost
      nonnegative (locallyFiniteTerminalWalk canonical)
    simpa only [locallyFiniteTerminalWalk_cost] using bound
  · have bound := ((locallyFiniteRuleSystem canonical).ruleNetwork 0).potential_difference_le_weightedDistance
      (locallyFiniteRuleSystem_connected canonical 0)
      (locallyFiniteMetricPotential_lipschitz canonical lengths nonnegative) (0 : Fin 6) (5 : Fin 6)
    cases canonical <;>
      simpa [locallyFiniteMetricHeight, locallyFiniteRuleDistance, abs_mul,
        abs_of_nonneg (nonnegative 0), mul_comm] using bound

theorem locallyFiniteRuleSystem_massMatrixR (canonical : Bool) :
    massMatrixR (locallyFiniteRuleSystem canonical).toRuleData = fun _ _ => (6 : ℝ) := by
  funext row column
  simp only [massMatrixR, locallyFiniteRuleSystem_massMatrix, Nat.cast_ofNat]

theorem locallyFiniteRuleSystem_massSpectralRadius (canonical : Bool) :
    realMatrixSpectralRadius (massMatrixR (locallyFiniteRuleSystem canonical).toRuleData) = 6 := by
  apply realMatrixSpectralRadius_eq_positive_eigenvalue (by norm_num)
    _ (massMatrixR_nonneg _) (fun _ => 1) 6 (fun _ => zero_lt_one) (by norm_num)
  funext colour
  have colourZero : colour = 0 := Subsingleton.elim _ _
  subst colour
  simp [locallyFiniteRuleSystem_massMatrixR, Matrix.mulVec, dotProduct]

theorem locallyFiniteRuleSystem_resistanceSpectralRadius (canonical : Bool) :
    (locallyFiniteRuleSystem canonical).resistanceSpectralRadius
      (locallyFiniteRuleSystem_connected canonical) (locallyFiniteRuleSystem_distancePositive canonical) =
        locallyFiniteRuleResistance canonical := by
  symm
  apply (locallyFiniteRuleSystem canonical).resistanceSpectralRadius_eq_of_positive_eigenpair
    (locallyFiniteRuleSystem_connected canonical) (locallyFiniteRuleSystem_distancePositive canonical)
    (by cases canonical <;> norm_num [locallyFiniteRuleResistance])
    (vector := fun _ => 1) (fun _ => zero_lt_one)
  rw [locallyFiniteRuleSystem_Psi canonical _ (fun _ => zero_le_one)]
  funext colour
  simp

theorem locallyFiniteRuleSystem_distanceSpectralRadius (canonical : Bool) :
    (locallyFiniteRuleSystem canonical).distanceSpectralRadius
      (locallyFiniteRuleSystem_connected canonical) = locallyFiniteRuleDistance canonical := by
  obtain ⟨lengths, positive, ratePositive, normalized, eigenpair⟩ :=
    (locallyFiniteRuleSystem canonical).metricLengths_spectral_eigenpair
      (locallyFiniteRuleSystem_connected canonical) (locallyFiniteRuleSystem_loopless canonical)
      (locallyFiniteRuleSystem_edgesUnique canonical) (locallyFiniteRuleSystem_distancePositive canonical)
  rw [locallyFiniteRuleSystem_metricLengths canonical lengths (fun colour => (positive colour).le)] at eigenpair
  have coordinate := congrFun eigenpair 0
  simp only [Pi.smul_apply, smul_eq_mul] at coordinate
  have lengthPositive := positive 0
  nlinarith

end
end EIGS

#print axioms EIGS.locallyFiniteTerminalWalk_cost
#print axioms EIGS.locallyFiniteMetricHeight_edge
#print axioms EIGS.locallyFiniteMetricPotential_lipschitz
#print axioms EIGS.locallyFiniteRuleSystem_metricLengths
#print axioms EIGS.locallyFiniteRuleSystem_massMatrixR
#print axioms EIGS.locallyFiniteRuleSystem_massSpectralRadius
#print axioms EIGS.locallyFiniteRuleSystem_resistanceSpectralRadius
#print axioms EIGS.locallyFiniteRuleSystem_distanceSpectralRadius
