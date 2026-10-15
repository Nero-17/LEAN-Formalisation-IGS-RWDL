import RequestProject.Section2Concrete

/-! Closed-orthant compatibility of the resistance regularization.
The positive regularization converges to the existing Thomson functional
at every nonnegative resistance vector, rather than to an unidentified
extension value. Every individual flow supplies the required upper bound.
No minimizing flow, eigenpair, or convergence hypothesis is assumed. -/

namespace EIGS
noncomputable section
open Filter Topology
open scoped BigOperators

theorem ThomsonData.eval_regularization_tendsto {K : ℕ} (data : ThomsonData K)
    (resistances : Fin K → ℝ) (nonnegative : 0 ≤ resistances) :
    Tendsto (fun epsilon : ℝ => data.eval (resistances + epsilon • (fun _ : Fin K => (1 : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 (data.eval resistances)) := by
  obtain ⟨limit, convergence⟩ := data.eval_extension_exists nonnegative
  have lower : data.eval resistances ≤ limit := by
    apply ge_of_tendsto convergence
    filter_upwards [self_mem_nhdsWithin] with epsilon epsilonPositive
    apply data.eval_mono nonnegative
    intro colour
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    exact le_add_of_nonneg_right (le_of_lt epsilonPositive)
  have upper (flow : data.F) : limit ≤ data.energy flow resistances := by
    have continuousEnergy : Continuous (fun epsilon : ℝ =>
        data.energy flow (resistances + epsilon • (fun _ : Fin K => (1 : ℝ)))) := by
      simp only [ThomsonData.energy, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      fun_prop
    have energyLimit : Tendsto (fun epsilon : ℝ =>
        data.energy flow (resistances + epsilon • (fun _ : Fin K => (1 : ℝ))))
        (𝓝[>] (0 : ℝ)) (𝓝 (data.energy flow resistances)) := by
      simpa only [zero_smul, add_zero] using
        (continuousEnergy.tendsto 0).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto convergence energyLimit
    filter_upwards [self_mem_nhdsWithin] with epsilon epsilonPositive
    have regularizedNonnegative : 0 ≤ resistances + epsilon • (fun _ => (1 : ℝ)) := by
      intro colour
      simp only [Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      exact add_nonneg (nonnegative colour) (le_of_lt epsilonPositive)
    exact ciInf_le (data.bddBelow_energy regularizedNonnegative) flow
  have equality : limit = data.eval resistances := by
    apply le_antisymm _ lower
    exact le_ciInf upper
  simpa only [equality] using convergence

theorem RenormMap.apply_regularization_tendsto {K : ℕ} (renormalization : RenormMap K)
    (resistances : Fin K → ℝ) (nonnegative : 0 ≤ resistances) :
    Tendsto (fun epsilon : ℝ => renormalization.apply (resistances + epsilon • (fun _ : Fin K => (1 : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 (renormalization.apply resistances)) := by
  apply tendsto_pi_nhds.mpr
  intro colour
  exact (renormalization.coord colour).eval_regularization_tendsto resistances nonnegative

theorem Network.effRes_regularization_tendsto {K : ℕ} (network : Network K)
    (source sink : network.V) (connected : Nonempty (network.Flow source sink))
    (resistances : Fin K → ℝ) (nonnegative : 0 ≤ resistances) :
    Tendsto (fun epsilon : ℝ => network.effRes source sink connected
      (resistances + epsilon • (fun _ : Fin K => (1 : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 (network.effRes source sink connected resistances)) :=
  (network.toThomsonData source sink connected).eval_regularization_tendsto resistances nonnegative

theorem RuleSystem.Psi_regularization_tendsto {K : ℕ} (rules : RuleSystem K)
    (resistances : Fin K → ℝ) (nonnegative : 0 ≤ resistances) :
    Tendsto (fun epsilon : ℝ => rules.toRenormMap.apply (resistances + epsilon • (fun _ : Fin K => (1 : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 (rules.toRenormMap.apply resistances)) :=
  rules.toRenormMap.apply_regularization_tendsto resistances nonnegative

theorem EIGSData.Psi_regularization_tendsto {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (resistances : Fin K → ℝ) (nonnegative : 0 ≤ resistances) :
    Tendsto (fun epsilon : ℝ => (system.ruleFamily connected).Psi
      (resistances + epsilon • (fun _ : Fin K => (1 : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 ((system.ruleFamily connected).Psi resistances)) := by
  simpa only [EIGSData.ruleFamily_Psi] using
    (system.connectedRuleSystem connected).Psi_regularization_tendsto resistances nonnegative

end
end EIGS

#print axioms EIGS.ThomsonData.eval_regularization_tendsto
#print axioms EIGS.RenormMap.apply_regularization_tendsto
#print axioms EIGS.Network.effRes_regularization_tendsto
#print axioms EIGS.RuleSystem.Psi_regularization_tendsto
#print axioms EIGS.EIGSData.Psi_regularization_tendsto

