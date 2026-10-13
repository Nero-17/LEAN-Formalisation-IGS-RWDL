import RequestProject.Section31.WatchedChain

/-! Transport of actual killed finite-chain quantities through an embedding.
Only rows outside the terminal set must agree and remain in the embedded
carrier. Terminal transition rows and terminal costs may differ arbitrarily. -/

namespace IGS.Sec31

open scoped BigOperators Classical

noncomputable section

variable {Local Ambient : Type*} [Fintype Local] [Fintype Ambient]
    [DecidableEq Local] [DecidableEq Ambient]
    (localChain : FinChain Local) (ambientChain : FinChain Ambient)
    (embedding : Local ↪ Ambient) (localBoundary : Finset Local)
    (ambientBoundary : Finset Ambient)
    (boundaryMembership : ∀ source,
      embedding source ∈ ambientBoundary ↔ source ∈ localBoundary)
    (rowAgreement : ∀ source, source ∉ localBoundary → ∀ target,
      ambientChain.P (embedding source) (embedding target) = localChain.P source target)
    (rowSupport : ∀ source, source ∉ localBoundary → ∀ target,
      target ∉ Set.range embedding → ambientChain.P (embedding source) target = 0)

include rowAgreement rowSupport

theorem killedEmbedding_transition_sum (source : Local) (outside : source ∉ localBoundary)
    (values : Ambient → ℝ) :
    (∑ target, ambientChain.P (embedding source) target * values target) =
      ∑ target, localChain.P source target * values (embedding target) := by
  have restrictSum :
      (∑ target ∈ Finset.univ.image embedding,
        ambientChain.P (embedding source) target * values target) =
      ∑ target, ambientChain.P (embedding source) target * values target := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro target _ outsideImage
    have outsideRange : target ∉ Set.range embedding := by
      rintro ⟨preimage, rfl⟩
      exact outsideImage (Finset.mem_image.mpr ⟨preimage, Finset.mem_univ _, rfl⟩)
    rw [rowSupport source outside target outsideRange, zero_mul]
  rw [← restrictSum]
  rw [Finset.sum_image (fun first _ second _ equality => embedding.injective equality)]
  apply Finset.sum_congr rfl
  intro target _
  rw [rowAgreement source outside target]

include boundaryMembership

theorem killedEmbedding_notHit (time : ℕ) (source : Local) :
    notHit ambientChain ambientBoundary time (embedding source) =
      notHit localChain localBoundary time source := by
  induction time generalizing source with
  | zero => simp only [notHit, boundaryMembership]
  | succ time induction =>
      by_cases inside : source ∈ localBoundary
      · simp only [notHit, (boundaryMembership source).2 inside, inside, if_true]
      · have ambientOutside : embedding source ∉ ambientBoundary :=
          fun membership => inside ((boundaryMembership source).1 membership)
        simp only [notHit, ambientOutside, inside, if_false]
        rw [killedEmbedding_transition_sum localChain ambientChain embedding localBoundary
          rowAgreement rowSupport source inside]
        apply Finset.sum_congr rfl
        intro target _
        rw [induction]

theorem killedEmbedding_partialHit (time : ℕ) (source : Local) :
    partialHit ambientChain ambientBoundary time (embedding source) =
      partialHit localChain localBoundary time source := by
  unfold partialHit
  apply Finset.sum_congr rfl
  intro index _
  exact killedEmbedding_notHit localChain ambientChain embedding localBoundary ambientBoundary
    boundaryMembership rowAgreement rowSupport index source

theorem killedEmbedding_hitTime (source : Local) :
    hitTime ambientChain ambientBoundary (embedding source) =
      hitTime localChain localBoundary source := by
  unfold hitTime
  congr 1
  funext time
  exact killedEmbedding_partialHit localChain ambientChain embedding localBoundary ambientBoundary
    boundaryMembership rowAgreement rowSupport time source

/-- Costs need agree only at states visited before killing. In particular,
this applies to nonnegative excursion costs without any boundedness premise. -/
theorem killedEmbedding_cost
    (localDuration : Local → ℝ) (ambientDuration : Ambient → ℝ)
    (durationAgreement : ∀ source, source ∉ localBoundary →
      ambientDuration (embedding source) = localDuration source)
    (time : ℕ) (source : Local) :
    cost ambientChain ambientBoundary ambientDuration time (embedding source) =
      cost localChain localBoundary localDuration time source := by
  induction time generalizing source with
  | zero => rfl
  | succ time induction =>
      by_cases inside : source ∈ localBoundary
      · simp only [cost, (boundaryMembership source).2 inside, inside, if_true]
      · have ambientOutside : embedding source ∉ ambientBoundary :=
          fun membership => inside ((boundaryMembership source).1 membership)
        simp only [cost, ambientOutside, inside, if_false]
        rw [durationAgreement source inside,
          killedEmbedding_transition_sum localChain ambientChain embedding localBoundary
            rowAgreement rowSupport source inside]
        congr 1
        apply Finset.sum_congr rfl
        intro target _
        rw [induction]

/-- Equality of the actual total-cost expressions. A separately proved
local bound transfers through this equality; finiteness is not assumed here. -/
theorem killedEmbedding_costLim
    (localDuration : Local → ℝ) (ambientDuration : Ambient → ℝ)
    (durationAgreement : ∀ source, source ∉ localBoundary →
      ambientDuration (embedding source) = localDuration source)
    (source : Local) :
    costLim ambientChain ambientBoundary ambientDuration (embedding source) =
      costLim localChain localBoundary localDuration source := by
  unfold costLim
  congr 1
  funext time
  exact killedEmbedding_cost localChain ambientChain embedding localBoundary ambientBoundary
    boundaryMembership rowAgreement rowSupport localDuration ambientDuration durationAgreement time source

end
end IGS.Sec31

#print axioms IGS.Sec31.killedEmbedding_transition_sum
#print axioms IGS.Sec31.killedEmbedding_notHit
#print axioms IGS.Sec31.killedEmbedding_partialHit
#print axioms IGS.Sec31.killedEmbedding_hitTime
#print axioms IGS.Sec31.killedEmbedding_cost
#print axioms IGS.Sec31.killedEmbedding_costLim
