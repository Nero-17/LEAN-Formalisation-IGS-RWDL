import RequestProject.Section31.EIGSMetricCompletion

/-! Canonical old-vertex inclusion between any two actual Xi levels.
Common-union embedding injectivity proves composition without identifying
different vertex types or assuming an interlevel compatibility field. -/

namespace EIGS

variable {K : ℕ}

noncomputable def xiVertexInclusion (system : EIGSData K) (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel) (vertex : XiVtx system coarseLevel) : XiVtx system fineLevel :=
  xiVertexAtLevel system (xiVertexEmbedding system coarseLevel vertex) fineLevel
    ((xiUnionBirth_embedding_le system coarseLevel vertex).trans levelsOrdered)

theorem xiVertexEmbedding_inclusion (system : EIGSData K) (coarseLevel fineLevel : ℕ)
    (levelsOrdered : coarseLevel ≤ fineLevel) (vertex : XiVtx system coarseLevel) :
    xiVertexEmbedding system fineLevel (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex) =
      xiVertexEmbedding system coarseLevel vertex := xiVertexEmbedding_atLevel _ _ _ _

theorem xiVertexInclusion_refl (system : EIGSData K) (level : ℕ) (vertex : XiVtx system level) :
    xiVertexInclusion system level level le_rfl vertex = vertex :=
  xiVertexEmbedding_injective system level (xiVertexEmbedding_inclusion system level level le_rfl vertex)

theorem xiVertexInclusion_comp (system : EIGSData K) (firstLevel middleLevel lastLevel : ℕ)
    (firstOrdered : firstLevel ≤ middleLevel) (secondOrdered : middleLevel ≤ lastLevel)
    (vertex : XiVtx system firstLevel) :
    xiVertexInclusion system middleLevel lastLevel secondOrdered
      (xiVertexInclusion system firstLevel middleLevel firstOrdered vertex) =
      xiVertexInclusion system firstLevel lastLevel (firstOrdered.trans secondOrdered) vertex := by
  apply xiVertexEmbedding_injective system lastLevel
  rw [xiVertexEmbedding_inclusion, xiVertexEmbedding_inclusion, xiVertexEmbedding_inclusion]

theorem xiVertexEmbedding_forward (system : EIGSData K) (coarseLevel offset : ℕ)
    (vertex : XiVtx system coarseLevel) :
    xiVertexEmbedding system (coarseLevel + offset) (xiForward system coarseLevel offset vertex) =
      xiVertexEmbedding system coarseLevel vertex := by
  induction offset with
  | zero => rfl
  | succ offset induction => exact induction

theorem xiVertexInclusion_eq_forward (system : EIGSData K) (coarseLevel offset : ℕ)
    (vertex : XiVtx system coarseLevel) :
    xiVertexInclusion system coarseLevel (coarseLevel + offset) (Nat.le_add_right _ _) vertex =
      xiForward system coarseLevel offset vertex := by
  apply xiVertexEmbedding_injective system (coarseLevel + offset)
  rw [xiVertexEmbedding_inclusion, xiVertexEmbedding_forward]

end EIGS
