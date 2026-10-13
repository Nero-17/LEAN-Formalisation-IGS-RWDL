import RequestProject.Section1Vertices
import RequestProject.Section31.ExtendedTraceEnergy

/-!
# Weighted trace energies on the actual EIGS vertex union

The common vertex set is constructed from the canonical vertex normal form of
`Section1Vertices`: the original two endpoints, together with each new private
interior vertex tagged by its birth level.  Every finite vertex set embeds
injectively, the embeddings respect the actual old-vertex maps, and their
images exhaust the common set.

The weighted networks use exactly `XiEdge`, `XiEnds`, and `XiCol`; in
particular no simple-graph projection discards parallel edges.  The extended
energy and its domain are instantiated on those networks, and their Markov
property is proved.  Positive resistance parameters are used to define the
weighted networks; their selection from the nonlinear Perron theorem and the
one-cell trace identity remain separate obligations.

This file imports the canonical Section 1 module from the merged project.
For separate-checkout verification both project library paths must be present.
-/

namespace EIGS

open IGS.Sec31
open scoped ENNReal

variable {K : ℕ}

/-- The vertices born at the next substitution step, before embedding. -/
def XiNewVertices (system : EIGSData K) (level : ℕ) : Type :=
  Σ edge : XiEdge system.toRuleData level,
    {vertex : (system.rule (XiCol system.toRuleData level edge)).V //
      vertex ≠ system.plantPlus (XiCol system.toRuleData level edge) ∧
        vertex ≠ system.plantMinus (XiCol system.toRuleData level edge)}

instance (system : EIGSData K) (level : ℕ) : Fintype (XiNewVertices system level) := by
  unfold XiNewVertices
  infer_instance

/-- A concrete common vertex union with no repeated old vertices. -/
def XiVertexUnion (system : EIGSData K) : Type := Bool ⊕ Σ level : ℕ, XiNewVertices system level

instance (system : EIGSData K) : Countable (XiVertexUnion system) := by
  unfold XiVertexUnion
  infer_instance

def xiUnionBirth (system : EIGSData K) : XiVertexUnion system → ℕ
  | Sum.inl _ => 0
  | Sum.inr ⟨level, _⟩ => level + 1

/-- The common-space embedding follows the actual old/private vertex normal form. -/
def xiVertexEmbedding (system : EIGSData K) : (level : ℕ) → XiVtx system level → XiVertexUnion system
  | 0, originalVertex => Sum.inl originalVertex
  | level + 1, Sum.inl oldVertex => xiVertexEmbedding system level oldVertex
  | level + 1, Sum.inr newVertex => Sum.inr ⟨level, newVertex⟩

@[simp] theorem xiVertexEmbedding_old (system : EIGSData K) (level : ℕ)
    (vertex : XiVtx system level) :
    xiVertexEmbedding system (level + 1) (Sum.inl vertex) =
      xiVertexEmbedding system level vertex := rfl

theorem xiUnionBirth_embedding_le (system : EIGSData K) : ∀ level (vertex : XiVtx system level),
    xiUnionBirth system (xiVertexEmbedding system level vertex) ≤ level := by
  intro level
  induction level with
  | zero => intro vertex; exact Nat.zero_le 0
  | succ level induction =>
      intro vertex
      cases vertex with
      | inl oldVertex => exact (induction oldVertex).trans (Nat.le_succ level)
      | inr newVertex => exact le_rfl

theorem xiVertexEmbedding_injective (system : EIGSData K) : ∀ level,
    Function.Injective (xiVertexEmbedding system level) := by
  intro level
  induction level with
  | zero => exact Sum.inl_injective
  | succ level induction =>
      intro first second equality
      cases first with
      | inl first =>
          cases second with
          | inl second => exact congrArg Sum.inl (induction equality)
          | inr second =>
              have birthBound := xiUnionBirth_embedding_le system level first
              have birthEquality := congrArg (xiUnionBirth system) equality
              change xiUnionBirth system (xiVertexEmbedding system level first) = level + 1
                at birthEquality
              omega
      | inr first =>
          cases second with
          | inl second =>
              have birthBound := xiUnionBirth_embedding_le system level second
              have birthEquality := congrArg (xiUnionBirth system) equality
              change level + 1 = xiUnionBirth system (xiVertexEmbedding system level second)
                at birthEquality
              omega
          | inr second =>
              have privateEquality : first = second := by
                exact eq_of_heq (Sigma.mk.inj_iff.1 (Sum.inr.inj equality)).2
              exact congrArg Sum.inr privateEquality

def xiLevelVertices (system : EIGSData K) (level : ℕ) : Set (XiVertexUnion system) :=
  Set.range (xiVertexEmbedding system level)

theorem xiLevelVertices_succ_subset (system : EIGSData K) (level : ℕ) :
    xiLevelVertices system level ⊆ xiLevelVertices system (level + 1) := by
  rintro vertex ⟨finiteVertex, rfl⟩
  exact ⟨Sum.inl finiteVertex, rfl⟩

theorem xiVertexUnion_exhausted (system : EIGSData K) (vertex : XiVertexUnion system) :
    ∃ level, vertex ∈ xiLevelVertices system level := by
  cases vertex with
  | inl originalVertex => exact ⟨0, originalVertex, rfl⟩
  | inr privateVertex =>
      obtain ⟨level, newVertex⟩ := privateVertex
      exact ⟨level + 1, Sum.inr newVertex, rfl⟩

/-- The paper's weighted finite network, on exactly the canonical EIGS edges. -/
noncomputable def xiWeightedFiniteNetwork (system : EIGSData K) (resistanceRate : ℝ)
    (resistanceRatePositive : 0 < resistanceRate) (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour) (level : ℕ) :
    FiniteNetwork (XiVtx system level) where
  Edge := XiEdge system.toRuleData level
  fintypeEdge := inferInstance
  decEqEdge := inferInstance
  ends := XiEnds system level
  cond := fun edge => resistanceRate ^ level * (resistanceVector (XiCol system.toRuleData level edge))⁻¹
  cond_pos := fun edge => mul_pos (pow_pos resistanceRatePositive _)
    (inv_pos.2 (resistanceVectorPositive _))

noncomputable def xiUnionWeightedNetwork (system : EIGSData K) (resistanceRate : ℝ)
    (resistanceRatePositive : 0 < resistanceRate) (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour) (level : ℕ) :
    FiniteNetwork (XiVertexUnion system) :=
  (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
    resistanceVectorPositive level).mapVertices (xiVertexEmbedding system level)

theorem xiUnionWeightedNetwork_energy_eq (system : EIGSData K) (resistanceRate : ℝ)
    (resistanceRatePositive : 0 < resistanceRate) (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour) (level : ℕ)
    (values : XiVertexUnion system → ℝ) :
    (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive level).energy values =
      ∑ edge : XiEdge system.toRuleData level,
        (resistanceRate ^ level * (resistanceVector (XiCol system.toRuleData level edge))⁻¹) *
          (values (xiVertexEmbedding system level (XiTail system level edge)) -
            values (xiVertexEmbedding system level (XiHead system level edge))) ^ 2 := rfl

noncomputable def xiExtendedWeightedEnergy (system : EIGSData K) (resistanceRate : ℝ)
    (resistanceRatePositive : 0 < resistanceRate) (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour) :
    (XiVertexUnion system → ℝ) → ℝ≥0∞ :=
  extendedTraceEnergy (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive)

theorem xiExtendedWeightedEnergy_comp_le (system : EIGSData K) (resistanceRate : ℝ)
    (resistanceRatePositive : 0 < resistanceRate) (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (contraction : ℝ → ℝ)
    (contractionBound : ∀ first second, |contraction first - contraction second| ≤ |first - second|)
    (values : XiVertexUnion system → ℝ) :
    xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive (contraction ∘ values) ≤
      xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive values :=
  extendedTraceEnergy_comp_le _ contraction contractionBound values

end EIGS
