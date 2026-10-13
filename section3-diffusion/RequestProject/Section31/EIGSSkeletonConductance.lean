import RequestProject.Section31.EIGSCellStarExit

/-!
The actual skeleton return kernel and its effective conductances. The
previously verified first-hitting trace theorem supplies the probabilistic
profile. Zero-skeleton perturbation orthogonality and the actual bilinear
trace supply its flux; no conductance-kernel identity is assumed.
-/

namespace EIGS

open scoped BigOperators Classical
open Matrix IGS.Sec31

variable {K : ℕ}

/-- The fine Laplacian flux at a skeleton vertex equals the actual coarse
effective-conductance energy paired with that vertex's indicator. -/
theorem xiUnitTraceExtension_skeleton_flux (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (values : XiVtx system coarse → ℝ) (vertex : XiVtx system coarse) :
    ((XiSimpleGraph system (coarse + steps)).lapMatrix ℝ *ᵥ
        xiUnitTraceExtension system rule_connected coarse steps values)
        (xiForward system coarse steps vertex) =
      ((XiNetwork system coarse).potentialNetwork
        ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1)
          (fun _ => by norm_num) steps)).energyInner values
          (fun target => if target = vertex then 1 else 0) := by
  let potential := xiUnitTraceExtension system rule_connected coarse steps values
  let fine_indicator := fun target : XiVtx system (coarse + steps) =>
    if target = xiForward system coarse steps vertex then (1 : ℝ) else 0
  let traced_indicator := xiUnitTraceExtension system rule_connected coarse steps
    (fun target => if target = vertex then 1 else 0)
  let fine_network := (XiNetwork system (coarse + steps)).potentialNetwork
    (fun _ => 1) (fun _ => by norm_num)
  have minimum : ∀ competitor : XiVtx system (coarse + steps) → ℝ,
      (∀ target ∈ Set.range (xiForward system coarse steps),
        competitor target = potential target) →
      fine_network.energy potential ≤ fine_network.energy competitor := by
    intro competitor competitor_boundary
    apply xiUnitTraceExtension_minimal system rule_connected coarse steps values competitor
    intro target
    exact (competitor_boundary _ ⟨target, rfl⟩).trans
      (xiUnitTraceExtension_boundary system rule_connected coarse steps values target)
  have vanishes : ∀ target ∈ Set.range (xiForward system coarse steps),
      (fine_indicator - traced_indicator) target = 0 := by
    rintro _ ⟨target, rfl⟩
    simp only [Pi.sub_apply, fine_indicator, traced_indicator, xiUnitTraceExtension_boundary]
    by_cases equal : target = vertex
    · simp [equal]
    · simp [equal, (xiForward_injective system coarse steps).ne equal]
  have orthogonal := fine_network.energyInner_eq_zero_of_min
    (Set.range (xiForward system coarse steps)) potential potential (fun _ _ => rfl)
    minimum (fine_indicator - traced_indicator) vanishes
  have subtract_pairing : fine_network.energyInner potential (fine_indicator - traced_indicator) =
      fine_network.energyInner potential fine_indicator -
        fine_network.energyInner potential traced_indicator := by
    simp only [IGS.Sec31.FiniteNetwork.energyInner, Pi.sub_apply, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro edge _
    ring
  rw [subtract_pairing] at orthogonal
  have fine_pairing : fine_network.energyInner potential fine_indicator =
      ((XiSimpleGraph system (coarse + steps)).lapMatrix ℝ *ᵥ potential)
        (xiForward system coarse steps vertex) := by
    rw [(XiNetwork system (coarse + steps)).unit_energyInner_laplacian
      (xiNetwork_loopless system rule_connected rules_loopless _)
      (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent _)]
    simp only [fine_indicator, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl
  have coarse_pairing := xiUnitTraceExtension_energyInner system rule_connected coarse steps values
    (fun target => if target = vertex then 1 else 0)
  change fine_network.energyInner potential traced_indicator = _ at coarse_pairing
  rw [fine_pairing, coarse_pairing] at orthogonal
  exact sub_eq_zero.mp orthogonal

/-- One original walk step followed by its first return to the actual
coarse skeleton. Self returns are deliberately retained at this stage. -/
noncomputable def xiSkeletonReturnProbability (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) (source target : XiVtx system coarse) : ℝ :=
  ∑ neighbour : XiVtx system (coarse + steps),
    transProb (XiSimpleGraph system (coarse + steps))
      (xiForward system coarse steps source) neighbour *
    hitDistLim (xiGraphWalkChain system rule_connected (coarse + steps))
      (Finset.univ.image (xiForward system coarse steps)) neighbour
      (xiForward system coarse steps target)

/-- Effective coarse conductance between two actual coarse vertices,
computed from the actual nonlinear Psi iterate on their connecting edges. -/
noncomputable def xiSkeletonConductance (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) (source target : XiVtx system coarse) : ℝ :=
  ∑ edge : XiEdge system.toRuleData coarse,
    if (XiTail system coarse edge = source ∧ XiHead system coarse edge = target) ∨
        (XiTail system coarse edge = target ∧ XiHead system coarse edge = source) then
      (((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
        (XiCol system.toRuleData coarse edge))⁻¹ else 0

/-- Pairing two distinct vertex indicators gives minus their actual coarse
conductance, including every connecting oriented edge exactly once. -/
theorem xiSkeletonConductance_eq_negative_pairing (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) (source target : XiVtx system coarse) (distinct : source ≠ target) :
    ((XiNetwork system coarse).potentialNetwork
        ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1)
          (fun _ => by norm_num) steps)).energyInner
        (fun vertex => if vertex = target then 1 else 0)
        (fun vertex => if vertex = source then 1 else 0) =
      -xiSkeletonConductance system rule_connected coarse steps source target := by
  unfold IGS.Sec31.FiniteNetwork.energyInner Network.potentialNetwork xiSkeletonConductance
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  change (((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
      (XiCol system.toRuleData coarse edge))⁻¹ *
      ((if XiTail system coarse edge = target then 1 else 0) -
      (if XiHead system coarse edge = target then 1 else 0)) *
      ((if XiTail system coarse edge = source then 1 else 0) -
        (if XiHead system coarse edge = source then 1 else 0)) = _
  by_cases tail_source : XiTail system coarse edge = source <;>
    by_cases head_source : XiHead system coarse edge = source <;>
    by_cases tail_target : XiTail system coarse edge = target <;>
    by_cases head_target : XiHead system coarse edge = target <;>
    simp_all <;> ring

/-- The actual original walk's off-diagonal return probability multiplied
by its fine degree equals the true nonlinear effective coarse conductance.
This is the electrical identification missing from the old conditional
watched-chain template. -/
theorem xiSkeletonReturnProbability_mul_degree (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (source target : XiVtx system coarse) (distinct : source ≠ target) :
    ((XiSimpleGraph system (coarse + steps)).degree
        (xiForward system coarse steps source) : ℝ) *
      xiSkeletonReturnProbability system rule_connected coarse steps source target =
        xiSkeletonConductance system rule_connected coarse steps source target := by
  let profile := xiUnitTraceExtension system rule_connected coarse steps
    (fun vertex => if vertex = target then 1 else 0)
  have profile_source : profile (xiForward system coarse steps source) = 0 := by
    simp only [profile, xiUnitTraceExtension_boundary, if_neg distinct]
  have return_profile : xiSkeletonReturnProbability system rule_connected coarse steps source target =
      ∑ neighbour : XiVtx system (coarse + steps),
        transProb (XiSimpleGraph system (coarse + steps))
          (xiForward system coarse steps source) neighbour * profile neighbour := by
    unfold xiSkeletonReturnProbability
    apply Finset.sum_congr rfl
    intro neighbour _
    rw [xiGraphWalkChain_first_hitting_eq_trace system rule_connected rules_loopless rules_unique
      planting_nonadjacent coarse steps target neighbour]
  have degree_positive : 0 < (XiSimpleGraph system (coarse + steps)).degree
      (xiForward system coarse steps source) := by
    exact_mod_cast xiSimpleGraph_degree_positive system rule_connected (coarse + steps)
      (xiForward system coarse steps source)
  have weighted_sum :
      ((XiSimpleGraph system (coarse + steps)).degree
          (xiForward system coarse steps source) : ℝ) *
        xiSkeletonReturnProbability system rule_connected coarse steps source target =
      ∑ neighbour ∈ (XiSimpleGraph system (coarse + steps)).neighborFinset
          (xiForward system coarse steps source), profile neighbour := by
    rw [return_profile, transProb_smul_sum degree_positive profile]
    exact mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr degree_positive.ne') _
  have flux := xiUnitTraceExtension_skeleton_flux system rule_connected rules_loopless rules_unique
    planting_nonadjacent coarse steps (fun vertex => if vertex = target then 1 else 0) source
  have identified_flux : ((XiSimpleGraph system (coarse + steps)).lapMatrix ℝ *ᵥ profile)
      (xiForward system coarse steps source) =
      -xiSkeletonConductance system rule_connected coarse steps source target :=
    flux.trans (xiSkeletonConductance_eq_negative_pairing system rule_connected coarse steps
      source target distinct)
  rw [lapMatrix_mulVec_apply, profile_source, mul_zero, zero_sub] at identified_flux
  rw [weighted_sum]
  linarith

theorem xiSkeletonReturnProbability_row_sum (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) (source : XiVtx system coarse) :
    (∑ target, xiSkeletonReturnProbability system rule_connected coarse steps source target) = 1 := by
  let skeleton := Finset.univ.image (xiForward system coarse steps)
  have skeleton_nonempty : skeleton.Nonempty :=
    Finset.image_nonempty.mpr ⟨source, Finset.mem_univ _⟩
  have hits_skeleton : ∀ vertex, Filter.Tendsto
      (fun time => notHit (xiGraphWalkChain system rule_connected (coarse + steps))
        skeleton time vertex) Filter.atTop (nhds 0) := by
    intro vertex
    have summable := expExit_summable (xiSimpleGraph_connected system rule_connected (coarse + steps))
      (show (skeletonᶜ)ᶜ.Nonempty by simpa using skeleton_nonempty) vertex
    simpa only [xiGraphWalkChain, graphWalkChain_notHit] using summable.tendsto_atTop_zero
  have total_hitting : ∀ vertex,
      (∑ target : XiVtx system coarse,
        hitDistLim (xiGraphWalkChain system rule_connected (coarse + steps)) skeleton vertex
          (xiForward system coarse steps target)) = 1 := by
    intro vertex
    have image_sum :
        (∑ target ∈ skeleton,
          hitDistLim (xiGraphWalkChain system rule_connected (coarse + steps)) skeleton vertex target) =
        ∑ target : XiVtx system coarse,
          hitDistLim (xiGraphWalkChain system rule_connected (coarse + steps)) skeleton vertex
            (xiForward system coarse steps target) :=
      Finset.sum_image (fun first _ second _ same =>
        (xiForward_injective system coarse steps) same)
    rw [← image_sum]
    have supported :
        (∑ target ∈ skeleton,
          hitDistLim (xiGraphWalkChain system rule_connected (coarse + steps)) skeleton vertex target) =
        ∑ target : XiVtx system (coarse + steps),
          hitDistLim (xiGraphWalkChain system rule_connected (coarse + steps)) skeleton vertex target := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro target _ outside
      exact hitDistLim_eq_zero_of_not_mem _ skeleton outside vertex
    rw [supported]
    exact hitDistLim_sum _ skeleton hits_skeleton vertex
  unfold xiSkeletonReturnProbability
  rw [Finset.sum_comm]
  calc
    _ = ∑ neighbour : XiVtx system (coarse + steps),
        transProb (XiSimpleGraph system (coarse + steps))
          (xiForward system coarse steps source) neighbour *
          (∑ target : XiVtx system coarse,
            hitDistLim (xiGraphWalkChain system rule_connected (coarse + steps)) skeleton neighbour
              (xiForward system coarse steps target)) := by
      apply Finset.sum_congr rfl
      intro neighbour _
      exact (Finset.mul_sum _ _ _).symm
    _ = ∑ neighbour : XiVtx system (coarse + steps),
        transProb (XiSimpleGraph system (coarse + steps))
          (xiForward system coarse steps source) neighbour := by
      apply Finset.sum_congr rfl
      intro neighbour _
      rw [total_hitting, mul_one]
    _ = 1 := by
      apply transProb_sum
      exact_mod_cast xiSimpleGraph_degree_positive system rule_connected (coarse + steps)
        (xiForward system coarse steps source)

/-- The real return kernel, with row mass proved from almost-sure hitting
of the actual finite skeleton, on the original coarse vertex carrier. -/
noncomputable def xiSkeletonReturnChain (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) : FinChain (XiVtx system coarse) where
  P := xiSkeletonReturnProbability system rule_connected coarse steps
  P_nonneg source target := Finset.sum_nonneg fun neighbour _ =>
    mul_nonneg (transProb_nonneg _ _) (hitDistLim_nonneg _ _ _ _)
  P_sum := xiSkeletonReturnProbability_row_sum system rule_connected coarse steps

theorem xiSkeletonConductance_nonnegative (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) (source target : XiVtx system coarse) :
    0 ≤ xiSkeletonConductance system rule_connected coarse steps source target := by
  unfold xiSkeletonConductance
  apply Finset.sum_nonneg
  intro edge _
  split
  · exact (inv_pos.mpr (ruleFamily_Psi_iterate_positive system rule_connected
      (fun _ => 1) (fun _ => by norm_num) steps _)).le
  · exact le_rfl

theorem xiSkeletonConductance_diagonal (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (coarse steps : ℕ) (source : XiVtx system coarse) :
    xiSkeletonConductance system rule_connected coarse steps source source = 0 := by
  unfold xiSkeletonConductance
  apply Finset.sum_eq_zero
  intro edge _
  have cannot_loop : ¬ (XiTail system coarse edge = source ∧ XiHead system coarse edge = source) := by
    rintro ⟨tail_source, head_source⟩
    exact xiNetwork_loopless system rule_connected rules_loopless coarse edge
      (tail_source.trans head_source.symm)
  simp only [cannot_loop, or_self, if_false]

theorem xiSkeletonConductance_row_positive (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) (source : XiVtx system coarse) :
    0 < ∑ target, xiSkeletonConductance system rule_connected coarse steps source target := by
  have degree_positive : 0 < (XiSimpleGraph system coarse).degree source := by
    exact_mod_cast xiSimpleGraph_degree_positive system rule_connected coarse source
  obtain ⟨target, adjacent⟩ := ((XiSimpleGraph system coarse).degree_pos_iff_exists_adj source).mp
    degree_positive
  obtain ⟨edge, endpoints⟩ : ∃ edge : XiEdge system.toRuleData coarse,
      (XiTail system coarse edge = source ∧ XiHead system coarse edge = target) ∨
      (XiTail system coarse edge = target ∧ XiHead system coarse edge = source) := by
    rcases adjacent.2 with ⟨edge, tail_source, head_target⟩ | ⟨edge, tail_target, head_source⟩
    · exact ⟨edge, Or.inl ⟨tail_source, head_target⟩⟩
    · exact ⟨edge, Or.inr ⟨tail_target, head_source⟩⟩
  have entry_positive : 0 < xiSkeletonConductance system rule_connected coarse steps source target := by
    apply lt_of_lt_of_le (inv_pos.mpr (ruleFamily_Psi_iterate_positive system rule_connected
      (fun _ => 1) (fun _ => by norm_num) steps (XiCol system.toRuleData coarse edge)))
    unfold xiSkeletonConductance
    have term_bound := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun candidate : XiEdge system.toRuleData coarse =>
        if (XiTail system coarse candidate = source ∧ XiHead system coarse candidate = target) ∨
            (XiTail system coarse candidate = target ∧ XiHead system coarse candidate = source) then
          (((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
            (XiCol system.toRuleData coarse candidate))⁻¹ else 0)
      (fun candidate _ => by
        dsimp only
        split
        · exact (inv_pos.mpr (ruleFamily_Psi_iterate_positive system rule_connected
            (fun _ => 1) (fun _ => by norm_num) steps _)).le
        · exact le_rfl)
      (Finset.mem_univ edge)
    simpa only [if_pos endpoints] using term_bound
  exact entry_positive.trans_le (Finset.single_le_sum
    (fun target _ => xiSkeletonConductance_nonnegative system rule_connected coarse steps source target)
    (Finset.mem_univ target))

theorem xiSkeletonConductance_row_eq_degree_mul_escape (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (source : XiVtx system coarse) :
    (∑ target, xiSkeletonConductance system rule_connected coarse steps source target) =
      ((XiSimpleGraph system (coarse + steps)).degree
          (xiForward system coarse steps source) : ℝ) *
        (1 - xiSkeletonReturnProbability system rule_connected coarse steps source source) := by
  have entries : ∀ target,
      xiSkeletonConductance system rule_connected coarse steps source target =
        ((XiSimpleGraph system (coarse + steps)).degree
            (xiForward system coarse steps source) : ℝ) *
          (xiSkeletonReturnProbability system rule_connected coarse steps source target -
            if target = source then
              xiSkeletonReturnProbability system rule_connected coarse steps source source else 0) := by
    intro target
    by_cases equal : target = source
    · subst target
      rw [xiSkeletonConductance_diagonal system rule_connected rules_loopless]
      simp
    · rw [if_neg equal, sub_zero]
      exact (xiSkeletonReturnProbability_mul_degree system rule_connected rules_loopless rules_unique
        planting_nonadjacent coarse steps source target (Ne.symm equal)).symm
  simp_rw [entries]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    xiSkeletonReturnProbability_row_sum system rule_connected coarse steps source]
  simp

theorem xiSkeletonReturnChain_departure_positive (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (source : XiVtx system coarse) :
    0 < 1 - (xiSkeletonReturnChain system rule_connected coarse steps).P source source := by
  have positive := xiSkeletonConductance_row_positive system rule_connected coarse steps source
  rw [xiSkeletonConductance_row_eq_degree_mul_escape system rule_connected rules_loopless rules_unique
    planting_nonadjacent coarse steps source] at positive
  have degree_positive := xiSimpleGraph_degree_positive system rule_connected (coarse + steps)
    (xiForward system coarse steps source)
  change 0 < 1 - xiSkeletonReturnProbability system rule_connected coarse steps source source
  exact (mul_pos_iff_of_pos_left degree_positive).mp positive

/-- After actual self returns are deleted, the actual watched Xi walk is
exactly the conductance walk with the true effective coarse conductances.
The kernel equality and positive departure denominators are proved here. -/
theorem xiSkeleton_distinctJumpChain_eq_conductance (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) :
    distinctJumpChain (xiSkeletonReturnChain system rule_connected coarse steps)
        (xiSkeletonReturnChain_departure_positive system rule_connected rules_loopless rules_unique
          planting_nonadjacent coarse steps) =
      condChain (xiSkeletonConductance system rule_connected coarse steps)
        (xiSkeletonConductance_nonnegative system rule_connected coarse steps)
        (xiSkeletonConductance_row_positive system rule_connected coarse steps) := by
  apply FinChain.ext
  funext source target
  change (if source = target then 0 else
      xiSkeletonReturnProbability system rule_connected coarse steps source target) /
      (1 - xiSkeletonReturnProbability system rule_connected coarse steps source source) =
    xiSkeletonConductance system rule_connected coarse steps source target /
      (∑ vertex, xiSkeletonConductance system rule_connected coarse steps source vertex)
  by_cases equal : source = target
  · subst target
    rw [xiSkeletonConductance_diagonal system rule_connected rules_loopless]
    simp
  · rw [if_neg equal,
      xiSkeletonConductance_row_eq_degree_mul_escape system rule_connected rules_loopless rules_unique
        planting_nonadjacent coarse steps source,
      ← xiSkeletonReturnProbability_mul_degree system rule_connected rules_loopless rules_unique
        planting_nonadjacent coarse steps source target equal]
    have degree_nonzero := (xiSimpleGraph_degree_positive system rule_connected (coarse + steps)
      (xiForward system coarse steps source)).ne'
    have escape_nonzero := (xiSkeletonReturnChain_departure_positive system rule_connected
      rules_loopless rules_unique planting_nonadjacent coarse steps source).ne'
    change 1 - xiSkeletonReturnProbability system rule_connected coarse steps source source ≠ 0
      at escape_nonzero
    field_simp [degree_nonzero, escape_nonzero] <;> ring

end EIGS

#print axioms EIGS.xiUnitTraceExtension_skeleton_flux
#print axioms EIGS.xiSkeletonConductance_eq_negative_pairing
#print axioms EIGS.xiSkeletonReturnProbability_mul_degree
#print axioms EIGS.xiSkeletonReturnProbability_row_sum
#print axioms EIGS.xiSkeletonConductance_row_positive
#print axioms EIGS.xiSkeletonConductance_row_eq_degree_mul_escape
#print axioms EIGS.xiSkeletonReturnChain_departure_positive
#print axioms EIGS.xiSkeleton_distinctJumpChain_eq_conductance
