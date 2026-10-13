import RequestProject.Section2Network

/-!
# Positive resistance and the one-colour renormalisation eigenpair

The resistance lower bound is proved from Kirchhoff's unit-flow equation and
finite Cauchy--Schwarz. Consequently a one-colour rule system has a positive
renormalisation eigenpair without an external Perron--Frobenius input.
This file concerns the existing flow-defined network resistance. Identifying
the iterated renormalisation map with all substituted graph resistances remains
a separate obligation.
-/

namespace EIGS

open scoped BigOperators

namespace Network

variable {K : ℕ} (network : Network K)

theorem unit_energy_lower_bound (source sink : network.V)
    (flow : network.Flow source sink) :
    1 / ((Fintype.card network.E : ℝ) + 1) ≤
      network.energyNetwork flow.1 (fun _ => 1) := by
  classical
  have divergence_sum :
      (∑ edge, ((if network.tail edge = source then (1 : ℝ) else 0) -
        (if network.head edge = source then (1 : ℝ) else 0)) * flow.1 edge) = 1 := by
    simpa [Network.div, sub_mul, Finset.sum_sub_distrib] using flow.property source
  have coefficient_bound :
      (∑ edge : network.E,
        ((if network.tail edge = source then (1 : ℝ) else 0) -
         (if network.head edge = source then (1 : ℝ) else 0)) ^ 2) ≤
        (Fintype.card network.E : ℝ) := by
    calc
      _ ≤ ∑ _edge : network.E, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro edge _
        split_ifs <;> norm_num
      _ = _ := by simp
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset network.E)
    (fun edge => (if network.tail edge = source then (1 : ℝ) else 0) -
      (if network.head edge = source then (1 : ℝ) else 0)) flow.1
  rw [divergence_sum] at cauchy
  have energy_nonneg : 0 ≤ ∑ edge : network.E, (flow.1 edge) ^ 2 :=
    Finset.sum_nonneg fun edge _ => sq_nonneg _
  have unit_bound : 1 ≤ (Fintype.card network.E : ℝ) *
      ∑ edge : network.E, (flow.1 edge) ^ 2 := by
    exact le_trans (by simpa using cauchy)
      (mul_le_mul_of_nonneg_right coefficient_bound energy_nonneg)
  simp only [Network.energyNetwork, one_mul]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (Fintype.card network.E : ℝ) + 1)).2
  nlinarith

theorem effRes_one_pos (source sink : network.V)
    (connected : Nonempty (network.Flow source sink)) :
    0 < network.effRes source sink connected (fun _ => 1) := by
  letI := connected
  have lower : 1 / ((Fintype.card network.E : ℝ) + 1) ≤
      network.effRes source sink connected (fun _ => 1) := by
    rw [network.effRes_eq_iInf]
    exact le_ciInf fun flow => network.unit_energy_lower_bound source sink flow
  exact lt_of_lt_of_le (by positivity) lower

end Network

namespace RuleSystem

theorem monochrome_eigenpair (rules : RuleSystem 1) :
    0 < rules.toRenormMap.apply (fun _ => 1) 0 ∧
      rules.toRenormMap.apply (fun _ => 1) =
        rules.toRenormMap.apply (fun _ => 1) 0 • (fun _ => (1 : ℝ)) := by
  constructor
  · exact (rules.R 0).effRes_one_pos (rules.βplus 0) (rules.βminus 0)
      (rules.connected 0)
  · ext colour
    have : colour = (0 : Fin 1) := Subsingleton.elim _ _
    subst colour
    simp

theorem monochrome_iterate_exact (rules : RuleSystem 1) (level : ℕ) :
    rules.toRenormMap.apply^[level] (fun _ => 1) =
      (rules.toRenormMap.apply (fun _ => 1) 0) ^ level • (fun _ => (1 : ℝ)) := by
  exact rules.toRenormMap.iterate_eigen rules.monochrome_eigenpair.1.le
    rules.monochrome_eigenpair.2 level

/-- The positive-eigenvalue conclusion of Lemma 2.6 for a concrete one-colour
rule system, with no eigenpair-existence premise. -/
theorem monochrome_positive_eigenvalue_exists_unique (rules : RuleSystem 1) :
    ∃! rate : ℝ, 0 < rate ∧ ∃ vector : Fin 1 → ℝ,
      (∀ colour, 0 < vector colour) ∧
        rules.toRenormMap.apply vector = rate • vector := by
  refine ⟨rules.toRenormMap.apply (fun _ => 1) 0,
    ⟨rules.monochrome_eigenpair.1, (fun _ => 1),
      (fun _ => zero_lt_one), rules.monochrome_eigenpair.2⟩, ?_⟩
  rintro rate ⟨rate_pos, vector, vector_pos, eigenpair⟩
  exact rules.toRenormMap.eigenvalue_unique (by decide) vector_pos
    (fun _ => zero_lt_one) rate_pos rules.monochrome_eigenpair.1
    eigenpair rules.monochrome_eigenpair.2

/-- In one colour normalized iterates are already constant, so no projective
contraction or convergence assumption is needed for this conclusion. -/
theorem monochrome_normalized_iterate_exact (rules : RuleSystem 1) (level : ℕ) :
    (fun colour => rules.toRenormMap.apply^[level] (fun _ => 1) colour /
      (rules.toRenormMap.apply (fun _ => 1) 0) ^ level) = (fun _ => (1 : ℝ)) := by
  rw [rules.monochrome_iterate_exact]
  ext colour
  simp [ne_of_gt rules.monochrome_eigenpair.1]

end RuleSystem

end EIGS
