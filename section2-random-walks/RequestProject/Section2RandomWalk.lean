import Mathlib
import RequestProject.Section2ExitTime
import RequestProject.Section2Commute

/-!
# The probability layer: simple random walk and first-step analysis (Section 2)

The linear systems `ExitSystem` (`Section2ExitTime.lean`) and `HittingSystem`
(`Section2Commute.lean`) characterise *expected* exit / hitting times of the simple
random walk.  Until now those systems were used as `Prop`s — a walk whose expected
times solve the system was taken for granted.  This file supplies the missing
**probability layer**: it constructs the genuine simple random walk on a finite
connected graph and proves, by first-step analysis, that its expected exit and
hitting times really do satisfy those linear systems.

## The random walk

For a finite simple graph `G`, the simple random walk moves from `x` to a uniformly
chosen neighbour:

  `transProb G x y = (deg x)⁻¹` if `x ∼ y`, and `0` otherwise.

`transProb G x ·` is a genuine probability distribution on the vertices whenever
`deg x > 0` (`transProb_sum`); `rwStep` packages it as a `PMF`, i.e. one step of the
Markov chain.

## Survival probabilities and expected exit time

`surv G S n x` is the probability that a walk started at `x` has **not** left the
set `S` (equivalently, has not hit `Sᶜ`) within `n` steps.  It obeys the transition
recursion
  `surv 0 x = [x ∈ S]`,  `surv (n+1) x = [x ∈ S] · ∑_y transProb x y · surv n y`,
so `surv n x = P^x(τ_{Sᶜ} > n)`.  The expected exit time is then the tail sum
  `expExit G S x = ∑_{n} surv n x = E^x[τ_{Sᶜ}]`
(the identity `E[τ] = ∑_n P(τ > n)`).

## Main results

* `expExit_summable`: the tail sum converges (the walk exits in finite expected
  time), proved from connectivity via a geometric bound on the survival
  probabilities.
* `exitSystem_expExit`: `ExitSystem G S (expExit G S)` — first-step analysis: the
  honestly-defined expected exit time solves the Laplacian exit-time system.  By
  `ExitSystem.unique` it is therefore *the* solution used throughout Section 2.
* `hittingSystem_expHit`: `HittingSystem G z (expExit G {z}ᶜ)` — the corresponding
  statement for hitting a single vertex, feeding the commute-time identity
  `C = 2|E|·R`.
-/

namespace EIGS

open scoped BigOperators
open SimpleGraph Matrix Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Transition probabilities -/

/-- One-step transition probability of the simple random walk on `G`: from `x`, move
to a uniformly random neighbour. -/
noncomputable def transProb (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : ℝ :=
  if G.Adj x y then ((G.degree x : ℝ))⁻¹ else 0

variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma transProb_nonneg (x y : V) : 0 ≤ transProb G x y := by
  unfold transProb; split <;> positivity

lemma transProb_pos_of_adj {x y : V} (h : G.Adj x y) : 0 < transProb G x y := by
  unfold transProb;
  rw [ if_pos h ];
  exact inv_pos.mpr ( Nat.cast_pos.mpr ( G.degree_pos_iff_exists_adj x |>.2 ⟨ y, h ⟩ ) )

/-
The transition probabilities out of a vertex of positive degree sum to `1`.
-/
lemma transProb_sum {x : V} (hx : 0 < G.degree x) : ∑ y, transProb G x y = 1 := by
  unfold transProb;
  simp +decide [ ← Finset.sum_filter, SimpleGraph.degree, SimpleGraph.neighborFinset ];
  exact mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| by simpa [ SimpleGraph.degree, SimpleGraph.neighborFinset ] using hx )

/-
The Laplacian applied to `f`, in terms of degree and neighbour sum.
-/
lemma lapMatrix_mulVec_apply (f : V → ℝ) (x : V) :
    (G.lapMatrix ℝ *ᵥ f) x = (G.degree x : ℝ) * f x - ∑ u ∈ G.neighborFinset x, f u := by
  unfold lapMatrix; simp +decide [ Matrix.mulVec, dotProduct, Finset.sum_ite ] ;
  simp +decide [ sub_mul, Finset.sum_ite, SimpleGraph.neighborFinset ];
  simp +decide [ SimpleGraph.neighborSet, degMatrix ];
  simp +decide [ diagonal ]

/-
The averaged neighbour sum equals the transition-weighted sum.
-/
lemma transProb_smul_sum {x : V} (hx : 0 < G.degree x) (f : V → ℝ) :
    ∑ y, transProb G x y * f y = (G.degree x : ℝ)⁻¹ * ∑ u ∈ G.neighborFinset x, f u := by
  rw [ Finset.mul_sum _ _ _ ];
  rw [ ← Finset.sum_subset ( show G.neighborFinset x ⊆ Finset.univ from Finset.subset_univ _ ) ];
  · exact Finset.sum_congr rfl fun y hy => by unfold transProb; aesop;
  · unfold transProb; aesop;

/-
The `ENNReal` transition weights out of a vertex of positive degree sum to `1`.
-/
lemma transProb_ofReal_sum {x : V} (hx : 0 < G.degree x) :
    ∑ y, ENNReal.ofReal (transProb G x y) = 1 := by
  rw [ ← ENNReal.ofReal_sum_of_nonneg ];
  · rw [ transProb_sum hx, ENNReal.ofReal_one ];
  · exact fun _ _ => transProb_nonneg _ _

/-- One step of the simple random walk as a probability distribution on the
vertices (defined at vertices of positive degree). -/
noncomputable def rwStep {x : V} (hx : 0 < G.degree x) : PMF V :=
  PMF.ofFintype (fun y => ENNReal.ofReal (transProb G x y)) (transProb_ofReal_sum hx)

@[simp] lemma rwStep_apply {x : V} (hx : 0 < G.degree x) (y : V) :
    rwStep hx y = ENNReal.ofReal (transProb G x y) := by
  simp [rwStep]

/-! ### Survival probabilities -/

/-- `surv G S n x = P^x(τ_{Sᶜ} > n)`: probability that the walk started at `x` stays
inside `S` for the first `n` steps. -/
noncomputable def surv (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ℕ → V → ℝ
  | 0, x => if x ∈ S then 1 else 0
  | (n+1), x => if x ∈ S then ∑ y, transProb G x y * surv G S n y else 0

lemma surv_zero_of_notMem {S : Finset V} {x : V} (hx : x ∉ S) (n : ℕ) :
    surv G S n x = 0 := by
  cases n <;> simp [surv, hx]

lemma surv_nonneg {S : Finset V} (n : ℕ) (x : V) : 0 ≤ surv G S n x := by
  induction' n with n ih generalizing x;
  · exact by unfold surv; split_ifs <;> norm_num;
  · exact (by rw [surv] ; split_ifs <;> [exact Finset.sum_nonneg (fun _ _ => mul_nonneg (transProb_nonneg _ _) (ih _)); exact le_refl 0])

lemma surv_le_one {S : Finset V} (n : ℕ) (x : V) : surv G S n x ≤ 1 := by
  induction' n with n ih generalizing x <;> simp_all +decide [ surv ];
  · split_ifs <;> norm_num;
  · split_ifs;
    · refine' le_trans ( Finset.sum_le_sum fun y _ => mul_le_of_le_one_right ( transProb_nonneg _ _ ) ( ih _ ) ) _;
      by_cases hx : 0 < G.degree x <;> simp_all +decide [ transProb ];
      simp +decide [ Finset.sum_ite, hx.ne' ];
      exact div_le_one_of_le₀ ( mod_cast by simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ] ) ( Nat.cast_nonneg _ );
    · norm_num

lemma surv_succ_le {S : Finset V} (n : ℕ) (x : V) : surv G S (n+1) x ≤ surv G S n x := by
  induction' n with n ih generalizing x;
  · by_cases hx : x ∈ S <;> simp +decide [ hx, surv ];
    by_cases hx' : 0 < G.degree x;
    · exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => transProb_nonneg _ _ ) ( by simpa [ hx' ] using transProb_sum hx' |> le_of_eq );
    · simp_all +decide [ transProb ];
  · by_cases hx : x ∈ S;
    · -- By definition of `surv`, we have:
      have h_surv_succ : surv G S (n + 2) x = ∑ y, transProb G x y * surv G S (n + 1) y ∧ surv G S (n + 1) x = ∑ y, transProb G x y * surv G S n y := by
        exact ⟨ if_pos hx, if_pos hx ⟩;
      exact h_surv_succ.1.symm ▸ h_surv_succ.2.symm ▸ Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ( ih y ) ( transProb_nonneg _ _ );
    · simp +decide [ *, surv ]

lemma surv_antitone {S : Finset V} (x : V) : Antitone (fun n => surv G S n x) := by
  exact antitone_nat_of_succ_le fun n => surv_succ_le n x

lemma surv_le_of_le {S : Finset V} {n m : ℕ} (h : n ≤ m) (x : V) :
    surv G S m x ≤ surv G S n x :=
  surv_antitone x h

/-
Along a walk from `x` to a vertex `z ∉ S`, the survival probability after
`p.length` steps is strictly below `1`: there is a positive-probability trajectory
that exits `S`.
-/
lemma surv_walk_lt {S : Finset V} {x z : V} (p : G.Walk x z) (hz : z ∉ S) :
    surv G S p.length x < 1 := by
  revert hz;
  induction' p with x y p ih;
  · exact fun hx => by rw [ show Walk.nil.length = 0 from rfl ] ; exact by rw [ show surv G S 0 x = if x ∈ S then 1 else 0 from rfl ] ; aesop;
  · by_cases hy : y ∈ S <;> simp_all +decide [ surv ];
    intro hi;
    rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ p ) ];
    refine' lt_of_lt_of_le ( add_lt_add_of_lt_of_le ( mul_lt_mul_of_pos_left ( ‹ih ∉ S → surv G S _ p < 1› hi ) ( transProb_pos_of_adj ‹_› ) ) ( Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left ( surv_le_one _ _ ) ( transProb_nonneg _ _ ) ) ) _;
    simp +decide [ ← Finset.sum_mul _ _ _, transProb_sum ( show 0 < G.degree y from G.degree_pos_iff_nonempty.mpr ⟨ p, by tauto ⟩ ) ]

/-
On a connected graph with nonempty `Sᶜ`, after `card V` steps the survival
probability is `< 1` from every vertex.
-/
lemma surv_card_lt (hG : G.Connected) {S : Finset V} (hS : Sᶜ.Nonempty) (x : V) :
    surv G S (Fintype.card V) x < 1 := by
  obtain ⟨ z, hz ⟩ := hS;
  -- By `hG.preconnected x z`, there exists a walk `p : G.Walk x z`.
  obtain ⟨ p, hp ⟩ : ∃ p : G.Walk x z, True := by
    have := hG x z; aesop;
  -- Consider the path associated to `p`, given by `p.toPath : G.Path x z`.
  -- Its underlying walk `(p.toPath : G.Walk x z)` is a path, so length `≤ card V - 1`.
  have hl : (p.toPath : G.Walk x z).length < Fintype.card V := by
    convert p.toPath.2.length_lt;
  exact lt_of_le_of_lt ( surv_le_of_le ( by linarith ) _ ) ( surv_walk_lt _ ( by simpa using hz ) )

/-
The contraction estimate: shifting by `m` steps multiplies survival by at most
`M`, where `M` bounds all `m`-step survival probabilities.
-/
lemma surv_shift_le {S : Finset V} {m : ℕ} {M : ℝ} (hM : ∀ w, surv G S m w ≤ M)
    (n : ℕ) (x : V) : surv G S (n + m) x ≤ M * surv G S n x := by
  induction' n with n ih generalizing x <;> simp_all +decide [ Nat.succ_add, mul_add, add_mul, Finset.sum_add_distrib ];
  · by_cases hx : x ∈ S <;> simp_all +decide [ surv ];
    rw [ surv_zero_of_notMem hx ];
  · by_cases hx : x ∈ S <;> simp_all +decide [ surv ];
    simpa only [ Finset.mul_sum _ _ _, mul_left_comm ] using Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ( ih y ) ( transProb_nonneg _ _ )

/-! ### The expected exit time and its convergence -/

/-- Expected exit time from `S` (= expected hitting time of `Sᶜ`), defined as the
tail sum `∑_n P^x(τ_{Sᶜ} > n)` of survival probabilities. -/
noncomputable def expExit (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (x : V) : ℝ :=
  ∑' n, surv G S n x

/-
The expected exit time is finite: the survival series converges.
-/
lemma expExit_summable (hG : G.Connected) {S : Finset V} (hS : Sᶜ.Nonempty) (x : V) :
    Summable (fun n => surv G S n x) := by
  -- By definition of $M$, we know that $M < 1$.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ M < 1 ∧ ∀ w, surv G S (Fintype.card V) w ≤ M := by
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M ∈ Set.image (fun w => surv G S (Fintype.card V) w) (Finset.univ : Finset V) ∧ ∀ y ∈ Set.image (fun w => surv G S (Fintype.card V) w) (Finset.univ : Finset V), y ≤ M := by
      exact ⟨ Finset.max' ( Finset.image ( fun w => surv G S ( Fintype.card V ) w ) Finset.univ ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ x ) ⟩, by simpa using Finset.max'_mem ( Finset.image ( fun w => surv G S ( Fintype.card V ) w ) Finset.univ ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ x ) ⟩, fun y hy => Finset.le_max' _ _ <| by simpa using hy ⟩;
    exact ⟨ M, by obtain ⟨ w, _, rfl ⟩ := hM.1; exact surv_nonneg _ _, by obtain ⟨ w, _, rfl ⟩ := hM.1; exact surv_card_lt hG hS w, fun w => hM.2 _ <| Set.mem_image_of_mem _ <| Finset.mem_univ _ ⟩;
  -- By induction on $k$, we show that $surv G S (m*k) x \leq M^k$.
  have h_induction : ∀ k : ℕ, surv G S (Fintype.card V * k) x ≤ M^k := by
    intro k;
    induction' k with k ih;
    · exact surv_le_one _ _;
    · convert surv_shift_le ( fun w => hM.2.2 w ) ( Fintype.card V * k ) x |> le_trans <| mul_le_mul_of_nonneg_left ih hM.1 using 1 ; ring;
  -- By induction on $k$, we show that $g N \leq m * \sum_{k=0}^{N-1} M^k$.
  have h_g_bound : ∀ N : ℕ, ∑ i ∈ Finset.range (Fintype.card V * N), surv G S i x ≤ (Fintype.card V : ℝ) * ∑ k ∈ Finset.range N, M^k := by
    intro N
    induction' N with N ih;
    · norm_num;
    · rw [ Nat.mul_succ, Finset.sum_range_add ];
      -- By the properties of the survival function, we have $\sum_{i=0}^{m-1} surv G S (m*N + i) x \leq m * M^N$.
      have h_sum_bound : ∑ i ∈ Finset.range (Fintype.card V), surv G S (Fintype.card V * N + i) x ≤ (Fintype.card V : ℝ) * M^N := by
        have h_sum_bound : ∀ i ∈ Finset.range (Fintype.card V), surv G S (Fintype.card V * N + i) x ≤ M^N := by
          intros i hi;
          exact le_trans ( surv_le_of_le ( by nlinarith [ Finset.mem_range.mp hi ] ) _ ) ( h_induction N );
        simpa using Finset.sum_le_sum h_sum_bound;
      simpa only [ Finset.sum_range_succ ] using by linarith;
  refine' summable_of_sum_range_le _ _;
  exact ( Fintype.card V : ℝ ) * ( 1 / ( 1 - M ) );
  · exact fun n => surv_nonneg n x;
  · intro n
    have h_sum_bound : ∑ i ∈ Finset.range n, surv G S i x ≤ ∑ i ∈ Finset.range (Fintype.card V * n), surv G S i x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( by nlinarith [ show Fintype.card V > 0 from Fintype.card_pos_iff.mpr ⟨ x ⟩ ] ) ) fun _ _ _ => surv_nonneg _ _;
    exact h_sum_bound.trans ( le_trans ( h_g_bound n ) ( mul_le_mul_of_nonneg_left ( by rw [ one_div, ← tsum_geometric_of_lt_one hM.1 hM.2.1 ] ; exact Summable.sum_le_tsum ( Finset.range n ) ( fun _ _ => pow_nonneg hM.1 _ ) ( summable_geometric_of_lt_one hM.1 hM.2.1 ) ) ( Nat.cast_nonneg _ ) ) )

lemma expExit_nonneg {S : Finset V} (x : V) : 0 ≤ expExit G S x :=
  tsum_nonneg fun n => surv_nonneg n x

lemma expExit_zero_of_notMem {S : Finset V} {x : V} (hx : x ∉ S) :
    expExit G S x = 0 := by
  unfold expExit
  simp [surv_zero_of_notMem hx]

/-! ### First-step analysis -/

/-
Degree positivity: a vertex of `S` has a neighbour, on a connected graph with
nonempty complement.
-/
lemma degree_pos_of_mem (hG : G.Connected) {S : Finset V} (hS : Sᶜ.Nonempty)
    {x : V} (hx : x ∈ S) : 0 < G.degree x := by
  by_contra h_contra;
  obtain ⟨ z, hz ⟩ := hS;
  obtain ⟨ p, hp ⟩ := hG x z;
  · aesop;
  · exact h_contra <| G.degree_pos_iff_exists_adj x |>.2 ⟨ _, by assumption ⟩

/-
First-step analysis (recurrence) for the expected exit time: for `x ∈ S`,
`expExit x = 1 + ∑_y transProb x y · expExit y`.
-/
lemma expExit_recurrence (hG : G.Connected) {S : Finset V} (hS : Sᶜ.Nonempty)
    {x : V} (hx : x ∈ S) :
    expExit G S x = 1 + ∑ y, transProb G x y * expExit G S y := by
  convert Summable.tsum_eq_zero_add ( expExit_summable hG hS x ) using 1;
  simp +decide [ hx, surv ];
  rw [ Summable.tsum_finsetSum ];
  · exact Finset.sum_congr rfl fun _ _ => by rw [ tsum_mul_left, expExit ] ;
  · exact fun y _ => Summable.mul_left _ ( expExit_summable hG hS y )

/-
**First-step analysis.** The honestly-defined expected exit time of the simple
random walk solves the Laplacian exit-time linear system.  Combined with
`ExitSystem.unique`, it is *the* exit-time solution used in Section 2.
-/
theorem exitSystem_expExit (hG : G.Connected) {S : Finset V} (hS : Sᶜ.Nonempty) :
    ExitSystem G S (expExit G S) := by
  refine' ⟨ fun x hx => expExit_zero_of_notMem hx, fun x hx => _ ⟩;
  rw [ lapMatrix_mulVec_apply ];
  rw [ expExit_recurrence hG hS hx ];
  rw [ transProb_smul_sum ( degree_pos_of_mem hG hS hx ) ];
  linarith [ inv_mul_cancel_left₀ ( show ( G.degree x : ℝ ) ≠ 0 by exact Nat.cast_ne_zero.mpr <| ne_of_gt <| degree_pos_of_mem hG hS hx ) <| ∑ u ∈ G.neighborFinset x, expExit G S u ]

/-
**First-step analysis for hitting a single vertex.** The expected hitting time
of `z` (= expected exit time from `{z}ᶜ`) solves the hitting-time linear system that
underlies the commute-time identity `C = 2|E|·R`.
-/
theorem hittingSystem_expHit (hG : G.Connected) (z : V) :
    HittingSystem G z (expExit G ({z}ᶜ)) := by
  convert exitSystem_expExit hG ( show ( { z }ᶜ : Finset V )ᶜ.Nonempty from by simp +decide ) using 1;
  ext; simp [HittingSystem, ExitSystem]

end EIGS