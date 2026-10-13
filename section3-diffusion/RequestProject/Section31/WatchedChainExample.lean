import RequestProject.Section31.TraceDecomposition

/-!
# A worked example for the watched skeleton chain

Reference: arXiv:2603.13798, §3.1, proof of Lemma 3.11.

The statements of `RequestProject.Section31.WatchedChain` carry several
hypotheses at once (a conductance range `[a,b]`, a descent function `ν`, a
uniform duration bound).  This file checks on the smallest possible skeleton —
the path `0 — 1 — 2` with the two terminals `B = {0,2}`, all edges of
conductance `1` — that they can all hold simultaneously, so that nothing above
is vacuous.

Here the constant produced by `condChain_expected_jumps_le` is
`C_R = N (card S · b / a)^N = 3`, while the true expected number of jumps from
the interior vertex is `1`; and with a uniform jump duration `d ≡ 1` the
accumulated cost is exactly `1`, well inside the bound `C_R · 1 = 3`.
-/

namespace IGS.Sec31

open Finset

namespace PathSkeleton

/-- Conductances of the path `0 — 1 — 2`: every edge has conductance `1`. -/
def cond : Fin 3 → Fin 3 → ℝ := ![![0, 1, 0], ![1, 0, 1], ![0, 1, 0]]

theorem cond_nonneg : ∀ z y, 0 ≤ cond z y := by
  intro z y
  fin_cases z <;> fin_cases y <;> simp [cond]

theorem cond_le_one : ∀ z y, cond z y ≤ 1 := by
  intro z y
  fin_cases z <;> fin_cases y <;> simp [cond]

theorem cond_sum_pos : ∀ z, 0 < ∑ y, cond z y := by
  intro z
  fin_cases z <;> simp [cond, Fin.sum_univ_three]

/-- The pair of terminals. -/
def term : Finset (Fin 3) := {0, 2}

/-- The distance to the terminals: `1` at the interior vertex, `0` at the
terminals. -/
def dist3 : Fin 3 → ℕ := fun z => if z = 1 then 1 else 0

theorem dist3_le_one : ∀ z, dist3 z ≤ 1 := by
  intro z; unfold dist3; split <;> omega

/-- The rule graph is connected to the terminals: the interior vertex has an
edge of conductance `1` to the terminal `0`. -/
theorem descent : ∀ z, z ∉ term → ∃ y, (1:ℝ) ≤ cond z y ∧ dist3 y < dist3 z := by
  intro z hz
  have hz1 : z = 1 := by
    fin_cases z <;> simp_all [term]
  subst hz1
  exact ⟨0, by simp [cond], by simp [dist3]⟩

/-- The walk really is a walk: from the interior vertex it jumps to either
terminal with probability `1/2`. -/
theorem step_half :
    (condChain cond cond_nonneg cond_sum_pos).P 1 0 = 1 / 2 := by
  show cond 1 0 / ∑ w, cond 1 w = 1 / 2
  simp [cond, Fin.sum_univ_three]
  norm_num

/-- **All the hypotheses hold**, and the expected number of skeleton jumps from
any vertex is at most `C_R = 3`. -/
theorem expected_jumps_le_three (z : Fin 3) :
    hitTime (condChain cond cond_nonneg cond_sum_pos) term z ≤ 3 := by
  have h := condChain_expected_jumps_le cond cond_nonneg cond_sum_pos term
    (a := 1) (b := 1) one_pos one_pos le_rfl cond_le_one dist3 le_rfl dist3_le_one
    descent z
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by simp
  rw [hcard] at h
  norm_num at h
  exact h

/-- The accumulated cost of the watched chain, for a uniform jump duration
`d ≡ 1`, is at most `C_R · 1 = 3` (the true value being `1`). -/
theorem costLim_le_three (z : Fin 3) :
    costLim (condChain cond cond_nonneg cond_sum_pos) term (fun _ => (1:ℝ)) z ≤ 3 := by
  have hpart := condChain_partialHit_le cond cond_nonneg cond_sum_pos term
    (a := 1) (b := 1) one_pos one_pos le_rfl cond_le_one dist3 le_rfl dist3_le_one
    descent z
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by simp
  simp only [hcard] at hpart
  norm_num at hpart
  have := costLim_le (condChain cond cond_nonneg cond_sum_pos) term
    (d := fun _ => (1:ℝ)) (D := 1) (R := 3) zero_le_one (fun _ => le_rfl) hpart
  simpa using this

/-- The cost accumulated from the interior vertex is exactly `1`: the walk makes
a single jump, of duration `1`. -/
theorem costLim_interior :
    costLim (condChain cond cond_nonneg cond_sum_pos) term (fun _ => (1:ℝ)) 1 = 1 := by
  set ch := condChain cond cond_nonneg cond_sum_pos with hch
  have hmem0 : (0 : Fin 3) ∈ term := by decide
  have hmem2 : (2 : Fin 3) ∈ term := by decide
  have hnot1 : (1 : Fin 3) ∉ term := by decide
  have hloop : ch.P (1 : Fin 3) 1 = 0 := by
    show cond 1 1 / ∑ w, cond 1 w = 0
    simp [cond]
  have hcost : ∀ k : ℕ, cost ch term (fun _ => (1:ℝ)) (k + 1) 1 = 1 := by
    intro k
    induction k with
    | zero =>
        rw [cost_succ ch term hnot1]
        simp [cost]
    | succ k _ =>
        rw [cost_succ ch term hnot1, Fin.sum_univ_three,
          cost_of_mem ch term hmem0, cost_of_mem ch term hmem2, hloop]
        ring
  have hle : ∀ k : ℕ, cost ch term (fun _ => (1:ℝ)) k 1 ≤ 1 := by
    intro k
    cases k with
    | zero => simp [cost]
    | succ k => exact le_of_eq (hcost k)
  refine le_antisymm (ciSup_le hle) ?_
  exact le_ciSup_of_le (f := fun k : ℕ => cost ch term (fun _ => (1:ℝ)) k 1)
    ⟨1, by rintro _ ⟨k, rfl⟩; exact hle k⟩ 1 (le_of_eq (hcost 0).symm)

/-!
### The excursion decomposition on the same example

With the skeleton taken to be the whole vertex set, the hypotheses of
`exit_time_le_skeleton_add_cost` (almost sure hitting of the skeleton, a uniform
bound on the time to reach it, a uniform bound on the excursions, and the
identification of the watched chain with a conductance walk) are all verified
here, so that theorem is not vacuous either.
-/

/-- The walk itself. -/
noncomputable def walk : FinChain (Fin 3) := condChain cond cond_nonneg cond_sum_pos

/-- The skeleton: here, all of the vertices. -/
def skel : Finset (Fin 3) := Finset.univ

theorem notHit_skel (k : ℕ) (v : Fin 3) : notHit walk skel k v = 0 :=
  notHit_of_mem walk skel (Finset.mem_univ v) k

theorem tendsto_notHit_skel (v : Fin 3) :
    Filter.Tendsto (fun k => notHit walk skel k v) Filter.atTop (nhds 0) := by
  simp only [notHit_skel]
  exact tendsto_const_nhds

theorem partialHit_skel (K : ℕ) (v : Fin 3) : partialHit walk skel K v ≤ 0 := by
  simp [partialHit, notHit_skel]

/-- The conductances of the watched chain: since the skeleton is everything, the
watched chain is the walk itself. -/
noncomputable def traceCond : {x // x ∈ skel} → {x // x ∈ skel} → ℝ :=
  fun z y => walk.P z.1 y.1

theorem traceCond_nonneg : ∀ z y, 0 ≤ traceCond z y := fun z y => walk.P_nonneg z.1 y.1

theorem traceCond_le_one : ∀ z y, traceCond z y ≤ 1 := fun z y => walk.P_le_one z.1 y.1

theorem traceCond_sum (z : {x // x ∈ skel}) : ∑ y, traceCond z y = 1 := by
  have h1 : ∑ y : {x // x ∈ skel}, walk.P z.1 y.1 = ∑ y ∈ skel, walk.P z.1 y :=
    Finset.sum_coe_sort skel fun y => walk.P z.1 y
  simpa [traceCond, skel] using h1.trans (walk.P_sum z.1)

theorem traceCond_sum_pos : ∀ z, 0 < ∑ y, traceCond z y := by
  intro z; rw [traceCond_sum z]; norm_num

/-- **The watched chain is the conductance walk** (here trivially, the skeleton
being the whole space): this is the analogue of the super-edge reduction. -/
theorem traceChain_eq :
    traceChain walk skel tendsto_notHit_skel
      = condChain traceCond traceCond_nonneg traceCond_sum_pos := by
  ext z y
  show ∑ u, walk.P z.1 u * hitDistLim walk skel u y.1
      = traceCond z y / ∑ y', traceCond z y'
  rw [traceCond_sum z, div_one]
  have hdirac : ∀ u : Fin 3, hitDistLim walk skel u y.1 = if u = y.1 then 1 else 0 :=
    fun u => hitDistLim_of_mem walk skel (Finset.mem_univ u) y.1
  simp [hdirac, traceCond]

/-- Each excursion takes one step. -/
theorem excursionTime_eq (w : {x // x ∈ skel}) : excursionTime walk skel w = 1 := by
  have h : ∀ u : Fin 3, hitTime walk skel u = 0 :=
    fun u => hitTime_of_mem walk skel (Finset.mem_univ u)
  simp [excursionTime, h]

/-- The descent hypothesis for the watched chain: from the interior vertex the
walk steps to a terminal with probability `1/2`. -/
theorem traceCond_descent : ∀ z, z ∉ termIn skel term →
    ∃ y, (1/2 : ℝ) ≤ traceCond z y ∧ (dist3 y.1) < (dist3 z.1) := by
  intro z hz
  have hz1 : z.1 = 1 := by
    have : z.1 ∉ term := by simpa using hz
    fin_cases z <;> simp_all [term]
  refine ⟨⟨0, Finset.mem_univ 0⟩, ?_, ?_⟩
  · show (1/2 : ℝ) ≤ walk.P z.1 0
    rw [hz1]
    exact le_of_eq (step_half).symm
  · simp [hz1, dist3]

/--
**The full decomposition, on the example.**
The expected time for the walk to reach the two terminals is at most
`R_S + D · C_R = 0 + 1 · 6 = 6` (the true value being `1` from the interior
vertex).  All the hypotheses of `exit_time_le_skeleton_add_cost` are verified
above, so the decomposition theorem is not vacuous.
-/
theorem exit_time_le_six (z : Fin 3) : hitTime walk term z ≤ 6 := by
  have hcard : (Fintype.card {x // x ∈ skel} : ℝ) = 3 := by simp [skel]
  have h := cell_exit_recursion_of_conductance_skeleton walk skel term
    tendsto_notHit_skel (RS := 0) (fun K v => partialHit_skel K v)
    traceCond traceCond_nonneg traceCond_sum_pos traceChain_eq
    (a := 1/2) (b := 1) (by norm_num) one_pos (by norm_num) traceCond_le_one
    (fun w => dist3 w.1) (N := 1) le_rfl (fun w => dist3_le_one w.1)
    traceCond_descent (Dstep := 1) zero_le_one
    (fun w => le_of_eq (excursionTime_eq w)) z
  rw [hcard] at h
  norm_num at h
  exact h

end PathSkeleton

end IGS.Sec31
