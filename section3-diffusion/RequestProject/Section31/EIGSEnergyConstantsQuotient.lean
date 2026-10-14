import RequestProject.Section31.EIGSAnchoredEnergyHilbert

/-! The null functions of the actual trace energy are exactly constants.
Subtracting the anchored value gives the unique representative vanishing at
the anchor, preserving energy. The resulting representative belongs to the
complete pure-energy Hilbert subspace constructed in EIGSAnchoredEnergyHilbert.
No resistance form or resistance metric is assumed.
Candidate source: compilation is not claimed. -/

namespace IGS.Sec31
variable {Vertex : Type*}

theorem FiniteNetwork.energy_sub_constant (network : FiniteNetwork Vertex)
    (values : Vertex → ℝ) (constant : ℝ) :
    network.energy (fun vertex => values vertex - constant) = network.energy values := by
  unfold FiniteNetwork.energy
  apply Finset.sum_congr rfl
  intro edge _
  congr 1
  ring

theorem traceEnergyDomain_sub_constant (networks : ℕ → FiniteNetwork Vertex)
    (values : traceEnergyDomain networks) (constant : ℝ) :
    (fun vertex => values.val vertex - constant) ∈ traceEnergyDomain networks := by
  obtain ⟨bound, boundValid⟩ := values.property
  refine ⟨bound, fun level => ?_⟩
  rw [FiniteNetwork.energy_sub_constant]
  exact boundValid level

theorem extendedTraceEnergy_sub_constant (networks : ℕ → FiniteNetwork Vertex)
    (values : Vertex → ℝ) (constant : ℝ) :
    extendedTraceEnergy networks (fun vertex => values vertex - constant) =
      extendedTraceEnergy networks values := by
  unfold extendedTraceEnergy
  simp only [FiniteNetwork.energy_sub_constant]

end IGS.Sec31

namespace EIGS
open IGS.Sec31
noncomputable section
variable {K : ℕ}

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (anchor : XiVertexUnion system)

theorem xiWeightedEnergy_zero_iff_constant
    (values : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive) :
    (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      values.val).toReal = 0 ↔ ∀ vertex, values.val vertex = values.val anchor := by
  constructor
  · intro zeroEnergy vertex
    let normalized : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive :=
      ⟨fun point => values.val point - values.val anchor,
        traceEnergyDomain_sub_constant _ values (values.val anchor)⟩
    obtain ⟨coefficient, _, control⟩ := exists_xiWeightedEnergy_anchored_evaluation system rulesConnected
      resistanceRate ratePositive resistanceVector vectorPositive anchor vertex
    have bound := control normalized
    have sameEnergy : xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        normalized.val = xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        values.val := extendedTraceEnergy_sub_constant _ values.val (values.val anchor)
    rw [sameEnergy, zeroEnergy] at bound
    change (values.val vertex - values.val anchor) ^ 2 ≤
      coefficient * (0 + (values.val anchor - values.val anchor) ^ 2) at bound
    simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, mul_zero] at bound
    nlinarith [sq_nonneg (values.val vertex - values.val anchor)]
  · intro constant
    have finiteZero : ∀ level, (xiUnionWeightedNetwork system resistanceRate ratePositive
        resistanceVector vectorPositive level).energy values.val = 0 := by
      intro level
      simp only [FiniteNetwork.energy, constant, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        mul_zero, Finset.sum_const_zero]
    change (extendedTraceEnergy _ values.val).toReal = 0
    simp only [extendedTraceEnergy, finiteZero, ENNReal.ofReal_zero, iSup_const, ENNReal.toReal_zero]

variable (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)

theorem exists_unique_xiEnergy_zero_anchored_representative
    (values : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive) :
    ∃! representative : xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair anchor,
      (∀ vertex, representative.val.value.val vertex = values.val vertex - values.val anchor) ∧
      ‖representative‖ ^ 2 =
        (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
          values.val).toReal := by
  let normalized : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive :=
    ⟨fun vertex => values.val vertex - values.val anchor,
      traceEnergyDomain_sub_constant _ values (values.val anchor)⟩
  let representative : xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor := ⟨⟨normalized⟩, sub_self _⟩
  refine ⟨representative, ⟨fun _ => rfl, ?_⟩, ?_⟩
  · rw [xiZeroAnchoredEnergyDomain_norm_sq]
    exact congrArg ENNReal.toReal (extendedTraceEnergy_sub_constant _ values.val (values.val anchor))
  · intro other property
    apply Subtype.ext
    apply (AnchoredTraceEnergySpace.equivDomain _ _ _ _).injective
    apply Subtype.ext
    funext vertex
    exact property.1 vertex

end
end EIGS

#print axioms EIGS.xiWeightedEnergy_zero_iff_constant
#print axioms EIGS.exists_unique_xiEnergy_zero_anchored_representative
