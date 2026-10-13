import RequestProject.Section31.DirichletThomson
import RequestProject.Section31.EIGSResistanceNormalization
import RequestProject.Section2Concrete
import Mathlib.Analysis.Normed.Group.Bounded

/-! Uniform prototype bounds are derived from actual connected finite rules.
Only an upper bound on the actual colour resistances is needed; no assumed
norm equivalence or assumed cellwise Poincaré estimate is used. -/

namespace EIGS

open scoped BigOperators

variable {K : ℕ}

theorem Network.unit_potential_energy_le (network : Network K)
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (upper : ℝ) (resistancesBounded : ∀ colour, resistances colour ≤ upper)
    (potential : network.V → ℝ) :
    (network.potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy potential ≤
      upper * (network.potentialNetwork resistances resistancesPositive).energy potential := by
  classical
  unfold IGS.Sec31.FiniteNetwork.energy Network.potentialNetwork
  simp only [inv_one, one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro edge _
  have coefficientBound : 1 ≤ upper * (resistances (network.color edge))⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (one_le_div (resistancesPositive _)).2 (resistancesBounded _)
  have differenceNonnegative := sq_nonneg (potential (network.tail edge) - potential (network.head edge))
  simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right coefficientBound differenceNonnegative

theorem Network.exists_uniform_zero_boundary_energy_bound (network : Network K)
    (connected : network.toSimpleGraph.Connected) (boundaryVertex : network.V) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ (resistances : Fin K → ℝ)
      (resistancesPositive : ∀ colour, 0 < resistances colour) (upper : ℝ),
      (∀ colour, resistances colour ≤ upper) →
      ∀ potential : network.V → ℝ, potential boundaryVertex = 0 → ∀ vertex,
        (potential vertex) ^ 2 ≤
          constant * upper * (network.potentialNetwork resistances resistancesPositive).energy potential := by
  obtain ⟨bound, boundNonnegative, potentialBound⟩ := network.exists_potential_poincare_constant
    (fun _ => 1) (fun _ => by norm_num) boundaryVertex connected
  refine ⟨bound + 1, by positivity, ?_⟩
  intro resistances resistancesPositive upper resistancesBounded potential boundaryZero vertex
  calc
    (potential vertex) ^ 2 ≤
        bound * (network.potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy potential :=
      potentialBound potential boundaryZero vertex
    _ ≤ (bound + 1) * (network.potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy potential :=
      mul_le_mul_of_nonneg_right (by linarith)
        ((network.potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy_nonneg potential)
    _ ≤ (bound + 1) * (upper * (network.potentialNetwork resistances resistancesPositive).energy potential) :=
      mul_le_mul_of_nonneg_left (network.unit_potential_energy_le resistances resistancesPositive upper resistancesBounded potential)
        (by positivity)
    _ = _ := by ring

theorem exists_rules_uniform_zero_boundary_energy_bound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ colour (resistances : Fin K → ℝ)
      (resistancesPositive : ∀ edgeColour, 0 < resistances edgeColour) (upper : ℝ),
      (∀ edgeColour, resistances edgeColour ≤ upper) →
      ∀ potential : (system.rule colour).V → ℝ,
      potential (system.plantPlus colour) = 0 → ∀ vertex,
        (potential vertex) ^ 2 ≤ constant * upper *
          ((system.ruleNetwork colour).potentialNetwork resistances resistancesPositive).energy potential := by
  classical
  choose constants constantsPositive potentialBound using fun colour =>
    (system.ruleNetwork colour).exists_uniform_zero_boundary_energy_bound (rulesConnected colour) (system.plantPlus colour)
  have sumPositive : 0 < ∑ colour, constants colour :=
    (constantsPositive system.initCol).trans_le
      (Finset.single_le_sum (fun colour _ => (constantsPositive colour).le) (Finset.mem_univ system.initCol))
  refine ⟨∑ colour, constants colour, sumPositive, ?_⟩
  intro colour resistances resistancesPositive upper resistancesBounded potential boundaryZero vertex
  have upperPositive : 0 < upper := (resistancesPositive system.initCol).trans_le (resistancesBounded system.initCol)
  have energyNonnegative := ((system.ruleNetwork colour).potentialNetwork resistances resistancesPositive).energy_nonneg potential
  have constantBound : constants colour ≤ ∑ edgeColour, constants edgeColour :=
    Finset.single_le_sum (fun edgeColour _ => (constantsPositive edgeColour).le) (Finset.mem_univ colour)
  exact (potentialBound colour resistances resistancesPositive upper resistancesBounded potential boundaryZero vertex).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right constantBound upperPositive.le) energyNonnegative)

theorem exists_xiResistance_iterate_upper_bound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ offset colour,
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour ≤ upper * resistanceRate ^ offset := by
  obtain ⟨_, _, convergence⟩ := exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected
    distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  obtain ⟨bound, normBound⟩ := (Metric.isBounded_range_of_tendsto _ convergence).exists_norm_le
  refine ⟨|bound| + 1, by positivity, ?_⟩
  intro offset colour
  apply (div_le_iff₀ (pow_pos ratePositive offset)).1
  have coordinateBound := norm_le_pi_norm
    (fun edgeColour => (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) edgeColour / resistanceRate ^ offset) colour
  have rangeBound := normBound _ ⟨offset, rfl⟩
  rw [Real.norm_eq_abs] at coordinateBound
  exact (le_abs_self _).trans (coordinateBound.trans (rangeBound.trans (by linarith [le_abs_self bound])))

theorem exists_xiStep_zero_boundary_energy_bound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ level (resistances : Fin K → ℝ)
      (resistancesPositive : ∀ colour, 0 < resistances colour) (upper : ℝ),
      (∀ colour, resistances colour ≤ upper) →
      ∀ values : XiVtx system (level + 1) → ℝ,
      (∀ vertex : XiVtx system level, values (Sum.inl vertex) = 0) →
      ∀ parent : XiEdge system.toRuleData level,
      ∀ vertex : (system.rule (XiCol system.toRuleData level parent)).V,
        (values ((XiNetwork system level).substEmbed (system.ruleFamily rulesConnected) parent vertex)) ^ 2 ≤
          constant * upper *
            ((system.ruleNetwork (XiCol system.toRuleData level parent)).potentialNetwork resistances resistancesPositive).energy
              (fun ruleVertex => values ((XiNetwork system level).substEmbed (system.ruleFamily rulesConnected) parent ruleVertex)) := by
  obtain ⟨constant, constantPositive, ruleBound⟩ := exists_rules_uniform_zero_boundary_energy_bound system rulesConnected
  refine ⟨constant, constantPositive, ?_⟩
  intro level resistances resistancesPositive upper resistancesBounded values oldZero parent vertex
  apply ruleBound (XiCol system.toRuleData level parent) resistances resistancesPositive upper resistancesBounded
    (fun ruleVertex => values ((XiNetwork system level).substEmbed (system.ruleFamily rulesConnected) parent ruleVertex)) _ vertex
  simpa [Network.substEmbed, EIGSData.ruleFamily, XiNetwork] using oldZero (XiTail system level parent)

end EIGS
