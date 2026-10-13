import RequestProject.Section31.EIGSUnitL2Recovery
import RequestProject.Section31.EIGSUnitEnergyRecovery

/-! The actual finite speed measure charges every vertex. Consequently a native
L² class has a unique everywhere-defined representative, and the original unit
graph energy descends to that actual L² space without a quotient ambiguity. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped ENNReal

variable {K : ℕ}

theorem xiVertexIncidenceCount_positive (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (level : ℕ) (vertex : XiVtx system level) :
    0 < xiVertexIncidenceCount system level vertex := by
  classical
  have terminalsDistinct : xiPositiveTerminal system level ≠ xiNegativeTerminal system level := by
    clear vertex
    induction level with
    | zero => exact Bool.false_ne_true
    | succ level induction => exact fun equality => induction (Sum.inl.inj equality)
  letI : Nontrivial (XiVtx system level) :=
    ⟨⟨xiPositiveTerminal system level, xiNegativeTerminal system level, terminalsDistinct⟩⟩
  obtain ⟨neighbor, adjacency⟩ :=
    (xiSimpleGraph_connected system rulesConnected level).preconnected.exists_adj_of_nontrivial vertex
  rcases adjacency with ⟨_, ⟨edge, tailEquality, _⟩ | ⟨edge, _, headEquality⟩⟩
  · haveI : Nonempty {edge : XiEdge system.toRuleData level // XiTail system level edge = vertex} :=
      ⟨⟨edge, tailEquality⟩⟩
    exact Nat.add_pos_iff_pos_or_pos.mpr (Or.inl Nat.card_pos)
  · haveI : Nonempty {edge : XiEdge system.toRuleData level // XiHead system level edge = vertex} :=
      ⟨⟨edge, headEquality⟩⟩
    exact Nat.add_pos_iff_pos_or_pos.mpr (Or.inr Nat.card_pos)

theorem xiVertexSpeedMeasure_singleton_positive (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ) (vertex : XiVtx system level) :
    0 < xiVertexSpeedMeasure system mass level {vertex} := by
  rw [xiVertexSpeedMeasure_singleton]
  apply ENNReal.div_pos
  · exact_mod_cast (ne_of_gt (xiVertexIncidenceCount_positive system rulesConnected level vertex))
  · finiteness

theorem xiVertexSpeedMeasure_ae_iff (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ) (predicate : XiVtx system level → Prop) :
    (∀ᵐ vertex ∂xiVertexSpeedMeasure system mass level, predicate vertex) ↔ ∀ vertex, predicate vertex := by
  rw [ae_iff_of_countable]
  exact ⟨fun almostEverywhere vertex => almostEverywhere vertex
    (ne_of_gt (xiVertexSpeedMeasure_singleton_positive system rulesConnected mass level vertex)),
    fun everywhere vertex _ => everywhere vertex⟩

theorem xiFiniteSpeedL2_apply (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ) (values : XiVtx system level → ℝ)
    (vertex : XiVtx system level) :
    xiFiniteSpeedL2 system mass level values vertex = values vertex :=
  (xiVertexSpeedMeasure_ae_iff system rulesConnected mass level _).1
    (xiFiniteSpeedL2_ae system mass level values) vertex

theorem xiFiniteSpeedL2_injective (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ) :
    Function.Injective (xiFiniteSpeedL2 system mass level) := by
  intro first second equality
  funext vertex
  have pointEquality := congrArg (fun function : Lp ℝ 2 (xiVertexSpeedMeasure system mass level) => function vertex) equality
  simpa only [xiFiniteSpeedL2_apply system rulesConnected] using pointEquality

theorem xiFiniteSpeedL2_representative (system : EIGSData K)
    (mass : XiMassParameters system) (level : ℕ)
    (function : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    xiFiniteSpeedL2 system mass level (fun vertex => function vertex) = function :=
  Lp.toLp_coeFn function _

theorem xiFiniteSpeedL2_unique_representative (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ)
    (function : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    ∃! values : XiVtx system level → ℝ, xiFiniteSpeedL2 system mass level values = function := by
  refine ⟨fun vertex => function vertex, xiFiniteSpeedL2_representative system mass level function, ?_⟩
  intro values equality
  apply xiFiniteSpeedL2_injective system rulesConnected mass level
  exact equality.trans (xiFiniteSpeedL2_representative system mass level function).symm

noncomputable def xiNativeScaledUnitEnergy (system : EIGSData K)
    (mass : XiMassParameters system) (resistanceRate normalization : ℝ) (level : ℕ)
    (function : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) : ℝ :=
  xiScaledUnitEnergy system resistanceRate normalization level (fun vertex => function vertex)

theorem xiNativeScaledUnitEnergy_finiteSpeedL2 (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (resistanceRate normalization : ℝ) (level : ℕ)
    (values : XiVtx system level → ℝ) :
    xiNativeScaledUnitEnergy system mass resistanceRate normalization level
      (xiFiniteSpeedL2 system mass level values) =
        xiScaledUnitEnergy system resistanceRate normalization level values := by
  unfold xiNativeScaledUnitEnergy
  congr 1
  funext vertex
  exact xiFiniteSpeedL2_apply system rulesConnected mass level values vertex

theorem xiNativeScaledUnitEnergy_nonnegative (system : EIGSData K)
    (mass : XiMassParameters system) (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (level : ℕ) (function : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    0 ≤ xiNativeScaledUnitEnergy system mass resistanceRate normalization level function := by
  exact mul_nonneg (mul_nonneg normalizationNonnegative (pow_nonneg rateNonnegative level))
    (((XiNetwork system level).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy_nonneg _)

theorem xiNativeScaledUnitEnergy_zero (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (resistanceRate normalization : ℝ) (level : ℕ) :
    xiNativeScaledUnitEnergy system mass resistanceRate normalization level 0 = 0 := by
  have representativeZero : (fun vertex : XiVtx system level => (0 : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) vertex) = 0 := by
    funext vertex
    exact (xiVertexSpeedMeasure_ae_iff system rulesConnected mass level _).1
      (Lp.coeFn_zero ℝ 2 (xiVertexSpeedMeasure system mass level)) vertex
  unfold xiNativeScaledUnitEnergy
  rw [representativeZero]
  simp [xiScaledUnitEnergy, IGS.Sec31.FiniteNetwork.energy]

theorem xiNativeScaledUnitEnergy_unitNativeL2 (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (resistanceRate normalization : ℝ)
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ) (level : ℕ) :
    xiNativeScaledUnitEnergy system mass resistanceRate normalization level
      (xiUnitNativeL2 system rulesConnected mass initialLevel initialValues level) =
        xiUnitPotentialScaledEnergy system rulesConnected resistanceRate normalization initialLevel initialValues level := by
  by_cases afterInitial : initialLevel ≤ level
  · rw [xiUnitNativeL2, dif_pos afterInitial, xiUnitPotentialScaledEnergy, dif_pos afterInitial]
    exact xiNativeScaledUnitEnergy_finiteSpeedL2 system rulesConnected mass resistanceRate normalization level _
  · rw [xiUnitNativeL2, dif_neg afterInitial, xiUnitPotentialScaledEnergy, dif_neg afterInitial]
    exact xiNativeScaledUnitEnergy_zero system rulesConnected mass resistanceRate normalization level

end EIGS
