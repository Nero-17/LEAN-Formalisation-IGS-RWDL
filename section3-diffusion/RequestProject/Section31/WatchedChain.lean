import Mathlib
import RequestProject.Section31.ExitTime

/-!
# §3.1, Lemma 3.11: the watched skeleton chain

Reference: arXiv:2603.13798, §3.1, proof of Lemma `sec31_one_step_stay`
(Lemma 3.11), the paragraph "Uniform exit bound for cells".

The paper's argument for `T_s ≤ T_{s-1} + C_R C_⋆ (ρ(M)ρ(Ψ))^{s-1}` is:

* from any `z`, the expected hitting time of the level-one skeleton `V_1(H)`
  is at most `T_{s-1}`;
* observed at successive *distinct* skeleton vertices, the walk is the random
  walk on the rule graph whose colour-`j` edges carry the effective conductance
  of the corresponding `(s-1)`-step copy (super-edge reduction, Lemma 2.4);
* by Corollary 2.8 these conductances lie, after normalisation, in a fixed
  compact subset of `(0,∞)^K`, so the expected number of skeleton jumps before
  hitting the two terminals is at most a constant `C_R`;
* each jump lasts at most `C_⋆ (ρ(M)ρ(Ψ))^{s-1}` in expectation, uniformly
  (Lemma 2.22 applied inside `H` with parameter `s-1`);
* optional stopping composes the two.

This file proves the two probabilistic steps that the paper only asserts, in a
self-contained finite-state formulation.

* `hitTime_le_of_uniform_hit`, `hitTime_le_of_descent`: for *any* transition
  kernel on a finite state space, a uniform lower bound `p` on the one-step
  probability of moving strictly closer to the target set `B` (a "descent"
  function `ν`, i.e. connectivity of the skeleton to the two terminals) gives
  the explicit bound `E_z[σ_B] ≤ N / p^N`, `N = max ν`.  The bound depends only
  on `p` and `N`, which is exactly why a *compact* family of conductances
  yields a single constant `C_R`.
* `condChain`, `condChain_expected_jumps_le`: the instance the paper uses — the
  conductance walk on a finite graph whose conductances lie in `[a, b]` — for
  which `p = a / (card · b)`, so that `C_R = N (card · b / a)^N` depends only
  on the graph and on the compact conductance range.
* `costLim_le`: the optional-stopping (Wald) step in its discrete
  additive-functional form.  If every visited state carries an expected cost at
  most `D`, the expected cost accumulated before hitting `B` is at most
  `D · E_z[σ_B]`.
* `watched_chain_recursion`: the two combined, giving exactly the paper's
  recursion `T_s ≤ T_{s-1} + C_R C_⋆ q^{s-1}`, and `watched_chain_exit_bound`,
  which feeds it into `geometric_recursion_bound` to conclude
  `T_s ≤ C_T q^s`.

What stays an input, matching the paper's own citations: the identification of
the watched process with the conductance walk on the rule graph (Lemma 2.4 /
Corollary 2.8), the one-jump time bound (Lemma 2.22), and the decomposition of
the exit time as "time to reach the skeleton" plus "time accumulated by the
watched chain".
-/

namespace IGS.Sec31

open Finset

/-- A Markov transition kernel on a finite state space. -/
structure FinChain (S : Type*) [Fintype S] where
  /-- one-step transition probabilities -/
  P : S → S → ℝ
  P_nonneg : ∀ z y, 0 ≤ P z y
  P_sum : ∀ z, ∑ y, P z y = 1

variable {S : Type*} [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
@[ext] theorem FinChain.ext {ch₁ ch₂ : FinChain S} (h : ch₁.P = ch₂.P) : ch₁ = ch₂ := by
  cases ch₁; cases ch₂; simp_all

omit [DecidableEq S] in
theorem FinChain.P_le_one (ch : FinChain S) (z y : S) : ch.P z y ≤ 1 := by
  have h1 : ch.P z y ≤ ∑ y', ch.P z y' :=
    Finset.single_le_sum (fun y' _ => ch.P_nonneg z y') (Finset.mem_univ y)
  rw [ch.P_sum z] at h1
  exact h1

/-- `notHit ch B k z = P_z(σ_B > k)`, the probability that the chain started at
`z` has not visited `B` up to time `k`. -/
def notHit (ch : FinChain S) (B : Finset S) : ℕ → S → ℝ
  | 0, z => if z ∈ B then 0 else 1
  | (k + 1), z => if z ∈ B then 0 else ∑ y, ch.P z y * notHit ch B k y

/-- `partialHit ch B K z = E_z[σ_B ∧ K] = ∑_{k<K} P_z(σ_B > k)`. -/
def partialHit (ch : FinChain S) (B : Finset S) (K : ℕ) (z : S) : ℝ :=
  ∑ k ∈ range K, notHit ch B k z

/-- The expected hitting time `E_z[σ_B] = ∑_{k≥0} P_z(σ_B > k)`, as the
supremum of its partial sums. -/
noncomputable def hitTime (ch : FinChain S) (B : Finset S) (z : S) : ℝ :=
  ⨆ K : ℕ, partialHit ch B K z

section Basic

variable (ch : FinChain S) (B : Finset S)

theorem notHit_of_mem {z : S} (hz : z ∈ B) : ∀ k, notHit ch B k z = 0
  | 0 => by simp [notHit, hz]
  | (_ + 1) => by simp [notHit, hz]

theorem notHit_nonneg : ∀ (k : ℕ) (z : S), 0 ≤ notHit ch B k z
  | 0, z => by by_cases hz : z ∈ B <;> simp [notHit, hz]
  | (k + 1), z => by
      by_cases hz : z ∈ B
      · simp [notHit, hz]
      · simp only [notHit, hz, if_false]
        exact sum_nonneg fun y _ => mul_nonneg (ch.P_nonneg z y) (notHit_nonneg k y)

theorem notHit_le_one : ∀ (k : ℕ) (z : S), notHit ch B k z ≤ 1
  | 0, z => by by_cases hz : z ∈ B <;> simp [notHit, hz]
  | (k + 1), z => by
      by_cases hz : z ∈ B
      · simp [notHit, hz]
      · simp only [notHit, hz, if_false]
        calc ∑ y, ch.P z y * notHit ch B k y ≤ ∑ y, ch.P z y * 1 :=
              sum_le_sum fun y _ =>
                mul_le_mul_of_nonneg_left (notHit_le_one k y) (ch.P_nonneg z y)
          _ = 1 := by simpa using ch.P_sum z

theorem notHit_succ_le : ∀ (k : ℕ) (z : S), notHit ch B (k + 1) z ≤ notHit ch B k z
  | 0, z => by
      by_cases hz : z ∈ B
      · simp [notHit, hz]
      · simp only [notHit, hz, if_false]
        calc ∑ y, ch.P z y * notHit ch B 0 y ≤ ∑ y, ch.P z y * 1 :=
              sum_le_sum fun y _ =>
                mul_le_mul_of_nonneg_left (notHit_le_one ch B 0 y) (ch.P_nonneg z y)
          _ = 1 := by simpa using ch.P_sum z
  | (k + 1), z => by
      by_cases hz : z ∈ B
      · simp [notHit, hz]
      · simp only [notHit, hz, if_false]
        exact sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (notHit_succ_le k y) (ch.P_nonneg z y)

theorem notHit_antitone {k l : ℕ} (hkl : k ≤ l) (z : S) :
    notHit ch B l z ≤ notHit ch B k z := by
  induction l with
  | zero => simp [Nat.le_zero.mp hkl]
  | succ l ih =>
      rcases Nat.lt_or_ge k (l + 1) with h | h
      · exact le_trans (notHit_succ_le ch B l z) (ih (Nat.lt_succ_iff.mp h))
      · have : k = l + 1 := le_antisymm hkl h
        simp [this]

/-- Markov step: if the chain fails to hit `B` in `b` steps from anywhere with
probability at most `c`, then `P_z(σ_B > a + b) ≤ c · P_z(σ_B > a)`. -/
theorem notHit_add_le {b : ℕ} {c : ℝ}
    (hb : ∀ w, notHit ch B b w ≤ c) :
    ∀ (a : ℕ) (z : S), notHit ch B (a + b) z ≤ c * notHit ch B a z := by
  intro a
  induction a with
  | zero =>
      intro z
      by_cases hz : z ∈ B
      · simp [notHit_of_mem ch B hz, notHit, hz]
      · simpa [notHit, hz] using hb z
  | succ a ih =>
      intro z
      by_cases hz : z ∈ B
      · simp [notHit_of_mem ch B hz]
      · have hrw : a + 1 + b = (a + b) + 1 := by omega
        rw [hrw]
        simp only [notHit, hz, if_false]
        calc ∑ y, ch.P z y * notHit ch B (a + b) y
            ≤ ∑ y, ch.P z y * (c * notHit ch B a y) :=
              sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (ih y) (ch.P_nonneg z y)
          _ = c * ∑ y, ch.P z y * notHit ch B a y := by
              rw [mul_sum]; exact sum_congr rfl fun y _ => by ring

theorem partialHit_nonneg (K : ℕ) (z : S) : 0 ≤ partialHit ch B K z :=
  sum_nonneg fun k _ => notHit_nonneg ch B k z

theorem partialHit_mono {K L : ℕ} (hKL : K ≤ L) (z : S) :
    partialHit ch B K z ≤ partialHit ch B L z := by
  apply sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset_range.mpr hKL
  · exact fun k _ _ => notHit_nonneg ch B k z

end Basic

section UniformHit

variable (ch : FinChain S) (B : Finset S)

/-- Iterating the Markov step: if the chain hits `B` within `N` steps from any
state with probability at least `1 - M`, then `P_z(σ_B > jN) ≤ M^j`. -/
theorem notHit_mul_le {N : ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ w, notHit ch B N w ≤ M) :
    ∀ (j : ℕ) (z : S), notHit ch B (j * N) z ≤ M ^ j := by
  intro j
  induction j with
  | zero => intro z; simpa using notHit_le_one ch B 0 z
  | succ j ih =>
      intro z
      have hrw : (j + 1) * N = j * N + N := by ring
      rw [hrw]
      calc notHit ch B (j * N + N) z ≤ M * notHit ch B (j * N) z :=
            notHit_add_le ch B hM _ z
        _ ≤ M * M ^ j := mul_le_mul_of_nonneg_left (ih z) hM0
        _ = M ^ (j + 1) := by ring

/-- Summing the geometric decay over blocks of length `N`. -/
theorem partialHit_block_le {N : ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ w, notHit ch B N w ≤ M) :
    ∀ (J : ℕ) (z : S), partialHit ch B (J * N) z ≤ N * ∑ j ∈ range J, M ^ j := by
  intro J
  induction J with
  | zero => intro z; simp [partialHit]
  | succ J ih =>
      intro z
      have hrw : (J + 1) * N = J * N + N := by ring
      have hsplit : partialHit ch B (J * N + N) z
          = partialHit ch B (J * N) z + ∑ i ∈ range N, notHit ch B (J * N + i) z := by
        simp [partialHit, sum_range_add]
      have htail : ∑ i ∈ range N, notHit ch B (J * N + i) z ≤ N * M ^ J := by
        calc ∑ i ∈ range N, notHit ch B (J * N + i) z
            ≤ ∑ _i ∈ range N, notHit ch B (J * N) z :=
              sum_le_sum fun i _ => notHit_antitone ch B (Nat.le_add_right _ i) z
          _ = N * notHit ch B (J * N) z := by simp [mul_comm]
          _ ≤ N * M ^ J :=
              mul_le_mul_of_nonneg_left (notHit_mul_le ch B hM0 hM J z) (Nat.cast_nonneg N)
      rw [hrw, hsplit, sum_range_succ, mul_add]
      exact add_le_add (ih z) htail

/--
**Expected number of jumps of the watched chain.**

If from every state the chain hits `B` within `N` steps with probability at
least `ε > 0`, then `E_z[σ_B] ≤ N / ε` — a bound depending on nothing but `N`
and `ε`.  This is the quantitative form of the paper's "the expected number of
skeleton jumps before hitting the two terminals is at most a constant `C_R`
depending only on the EIGS".
-/
theorem partialHit_le_of_uniform_hit {N : ℕ} {ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hhit : ∀ w, notHit ch B N w ≤ 1 - ε) (z : S) (K : ℕ) :
    partialHit ch B K z ≤ N / ε := by
  set M : ℝ := 1 - ε with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith
  have hgeom : ∀ J : ℕ, ∑ j ∈ range J, M ^ j ≤ 1 / ε := by
    intro J
    have h1 : (∑ j ∈ range J, M ^ j) * (M - 1) = M ^ J - 1 := geom_sum_mul M J
    have hM1 : M - 1 = -ε := by rw [hMdef]; ring
    have hMJ : 0 ≤ M ^ J := pow_nonneg hM0 J
    rw [hM1] at h1
    rw [le_div_iff₀ hε]
    nlinarith
  have hpart : ∀ K : ℕ, partialHit ch B K z ≤ (N : ℝ) / ε := by
    intro K
    have hKle : K ≤ K * N := Nat.le_mul_of_pos_right K (lt_of_lt_of_le Nat.zero_lt_one hN)
    calc partialHit ch B K z ≤ partialHit ch B (K * N) z := partialHit_mono ch B hKle z
      _ ≤ N * ∑ j ∈ range K, M ^ j := partialHit_block_le ch B hM0 hhit K z
      _ ≤ N * (1 / ε) := mul_le_mul_of_nonneg_left (hgeom K) (Nat.cast_nonneg N)
      _ = (N : ℝ) / ε := by ring
  exact hpart K

/-- The expected hitting time version of `partialHit_le_of_uniform_hit`. -/
theorem hitTime_le_of_uniform_hit {N : ℕ} {ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hhit : ∀ w, notHit ch B N w ≤ 1 - ε) (z : S) :
    hitTime ch B z ≤ N / ε :=
  ciSup_le (partialHit_le_of_uniform_hit ch B hN hε hε1 hhit z)

/--
**Connectivity gives the uniform hitting probability.**

If every state outside `B` has a one-step move of probability at least `p`
decreasing the "distance" `ν` to `B`, then from any state the chain hits `B`
within `k` steps with probability at least `p^k`, as soon as `ν z ≤ k`.
-/
theorem notHit_le_of_descent {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (nu : S → ℕ)
    (hdesc : ∀ z, z ∉ B → ∃ y, p ≤ ch.P z y ∧ nu y < nu z) :
    ∀ (k : ℕ) (z : S), nu z ≤ k → notHit ch B k z ≤ 1 - p ^ k := by
  intro k
  induction k with
  | zero =>
      intro z hz
      by_cases hzB : z ∈ B
      · simp [notHit, hzB]
      · obtain ⟨y, _, hy⟩ := hdesc z hzB
        omega
  | succ k ih =>
      intro z hz
      have hppow : (0:ℝ) < p ^ k := pow_pos hp0 k
      have hppow1 : p ^ (k + 1) ≤ 1 := pow_le_one₀ hp0.le hp1
      by_cases hzB : z ∈ B
      · simp only [notHit, hzB, if_true]
        linarith
      obtain ⟨y, hpy, hnuy⟩ := hdesc z hzB
      have hnuyk : nu y ≤ k := by omega
      have hyk : notHit ch B k y ≤ 1 - p ^ k := ih y hnuyk
      have hnn : ∀ w ∈ (univ : Finset S), 0 ≤ ch.P z w * (1 - notHit ch B k w) := by
        intro w _
        exact mul_nonneg (ch.P_nonneg z w) (by linarith [notHit_le_one ch B k w])
      have hsingle : ch.P z y * (1 - notHit ch B k y)
          ≤ ∑ w, ch.P z w * (1 - notHit ch B k w) :=
        Finset.single_le_sum hnn (mem_univ y)
      have hlow : p * p ^ k ≤ ch.P z y * (1 - notHit ch B k y) := by
        have h1 : p ^ k ≤ 1 - notHit ch B k y := by linarith
        have h2 : (0:ℝ) ≤ ch.P z y := ch.P_nonneg z y
        calc p * p ^ k ≤ ch.P z y * p ^ k :=
              mul_le_mul_of_nonneg_right hpy hppow.le
          _ ≤ ch.P z y * (1 - notHit ch B k y) := mul_le_mul_of_nonneg_left h1 h2
      have hsplit : ∑ w, ch.P z w * (1 - notHit ch B k w)
          = 1 - ∑ w, ch.P z w * notHit ch B k w := by
        have : ∑ w, ch.P z w * (1 - notHit ch B k w)
            = (∑ w, ch.P z w) - ∑ w, ch.P z w * notHit ch B k w := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun w _ => by ring
        rw [this, ch.P_sum z]
      simp only [notHit, hzB, if_false]
      have : p ^ (k + 1) = p * p ^ k := by ring
      linarith [hsingle, hlow, hsplit]

/--
**Expected number of skeleton jumps, explicit form.**

On a finite state space, a descent function `ν ≤ N` with uniform step
probability `p` gives `E_z[σ_B] ≤ N / p^N`.  Only `N` and `p` enter, which is
precisely why the compact family of traced conductances (Corollary 2.8) yields
a single constant `C_R` for all the copies.
-/
theorem partialHit_le_of_descent {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (nu : S → ℕ) {N : ℕ}
    (hN : 1 ≤ N) (hnu : ∀ z, nu z ≤ N)
    (hdesc : ∀ z, z ∉ B → ∃ y, p ≤ ch.P z y ∧ nu y < nu z) (z : S) (K : ℕ) :
    partialHit ch B K z ≤ N / p ^ N := by
  refine partialHit_le_of_uniform_hit ch B hN (pow_pos hp0 N) (pow_le_one₀ hp0.le hp1) ?_ z K
  intro w
  exact notHit_le_of_descent ch B hp0 hp1 nu hdesc N w (hnu w)

/-- The expected hitting time version of `partialHit_le_of_descent`. -/
theorem hitTime_le_of_descent {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (nu : S → ℕ) {N : ℕ}
    (hN : 1 ≤ N) (hnu : ∀ z, nu z ≤ N)
    (hdesc : ∀ z, z ∉ B → ∃ y, p ≤ ch.P z y ∧ nu y < nu z) (z : S) :
    hitTime ch B z ≤ N / p ^ N :=
  ciSup_le (partialHit_le_of_descent ch B hp0 hp1 nu hN hnu hdesc z)

end UniformHit

section Conductance

/--
**The conductance walk.**  This is the chain the paper's watched process is
identified with (super-edge reduction, Lemma 2.4): on the rule graph, the
colour-`j` edges carry the effective conductance of the corresponding
`(s-1)`-step copy.
-/
noncomputable def condChain (c : S → S → ℝ) (hc : ∀ z y, 0 ≤ c z y)
    (hpos : ∀ z, 0 < ∑ y, c z y) : FinChain S where
  P z y := c z y / ∑ w, c z w
  P_nonneg z y := div_nonneg (hc z y) (hpos z).le
  P_sum z := by
    rw [← Finset.sum_div, div_self (hpos z).ne']

omit [DecidableEq S] in
/--
**A compact conductance range gives a uniform step probability.**
If all conductances are at most `b` and the conductance of the edge `z → y` is
at least `a`, then the walk takes that edge with probability at least
`a / (card S · b)`.
-/
theorem condChain_step_lower (c : S → S → ℝ) (hc : ∀ z y, 0 ≤ c z y)
    (hpos : ∀ z, 0 < ∑ y, c z y) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hcb : ∀ z y, c z y ≤ b)
    {z y : S} (hay : a ≤ c z y) :
    a / (Fintype.card S * b) ≤ (condChain c hc hpos).P z y := by
  have hcard : 0 < (Fintype.card S : ℝ) := by
    have : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨z⟩
    exact_mod_cast this
  have hsum : ∑ w, c z w ≤ (Fintype.card S : ℝ) * b := by
    calc ∑ w, c z w ≤ ∑ _w : S, b := Finset.sum_le_sum fun w _ => hcb z w
      _ = (Fintype.card S : ℝ) * b := by simp [Finset.sum_const, mul_comm]
  show a / ((Fintype.card S : ℝ) * b) ≤ c z y / ∑ w, c z w
  rw [div_le_div_iff₀ (by positivity) (hpos z)]
  nlinarith [hpos z, hc z y]

/--
**Expected number of jumps for the conductance walk.**
Combining the two previous results: for a conductance walk whose conductances
lie in `[a, b]` along the descent edges, the expected hitting time of the
terminal set `B` is at most `C_R = N (card S · b / a)^N`.
-/
theorem condChain_partialHit_le (c : S → S → ℝ) (hc : ∀ z y, 0 ≤ c z y)
    (hpos : ∀ z, 0 < ∑ y, c z y) (B : Finset S) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (hcb : ∀ z y, c z y ≤ b) (nu : S → ℕ) {N : ℕ} (hN : 1 ≤ N)
    (hnu : ∀ z, nu z ≤ N)
    (hdesc : ∀ z, z ∉ B → ∃ y, a ≤ c z y ∧ nu y < nu z) (z : S) (K : ℕ) :
    partialHit (condChain c hc hpos) B K z ≤ N / (a / (Fintype.card S * b)) ^ N := by
  have hcard : 0 < (Fintype.card S : ℝ) := by
    have : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨z⟩
    exact_mod_cast this
  set p : ℝ := a / (Fintype.card S * b) with hp
  have hp0 : 0 < p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one (by positivity)]
    have h1 : (1:ℝ) ≤ (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨z⟩
    nlinarith
  refine partialHit_le_of_descent _ B hp0 hp1 nu hN hnu ?_ z K
  intro w hw
  obtain ⟨y, hay, hnuy⟩ := hdesc w hw
  exact ⟨y, condChain_step_lower c hc hpos ha.le hb hcb hay, hnuy⟩

/-- The expected hitting time version of `condChain_partialHit_le`: the
expected number of skeleton jumps is at most `C_R = N (card S · b / a)^N`. -/
theorem condChain_expected_jumps_le (c : S → S → ℝ) (hc : ∀ z y, 0 ≤ c z y)
    (hpos : ∀ z, 0 < ∑ y, c z y) (B : Finset S) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (hcb : ∀ z y, c z y ≤ b) (nu : S → ℕ) {N : ℕ} (hN : 1 ≤ N)
    (hnu : ∀ z, nu z ≤ N)
    (hdesc : ∀ z, z ∉ B → ∃ y, a ≤ c z y ∧ nu y < nu z) (z : S) :
    hitTime (condChain c hc hpos) B z ≤ N / (a / (Fintype.card S * b)) ^ N :=
  ciSup_le (condChain_partialHit_le c hc hpos B ha hb hab hcb nu hN hnu hdesc z)

end Conductance

section Cost

variable (ch : FinChain S) (B : Finset S)

/-- `cost ch B d k z` is the expected cost accumulated by the chain started at
`z` during its first `k` steps before hitting `B`, when a visit to the state
`w` costs `d w` (here: the expected duration of the skeleton jump started
at `w`). -/
def cost (ch : FinChain S) (B : Finset S) (d : S → ℝ) : ℕ → S → ℝ
  | 0, _ => 0
  | (k + 1), z => if z ∈ B then 0 else d z + ∑ y, ch.P z y * cost ch B d k y

/-- The total expected accumulated cost `E_z[∑_{k<σ_B} d(Z_k)]`. -/
noncomputable def costLim (ch : FinChain S) (B : Finset S) (d : S → ℝ) (z : S) : ℝ :=
  ⨆ k : ℕ, cost ch B d k z

theorem cost_of_mem {d : S → ℝ} {z : S} (hz : z ∈ B) : ∀ k, cost ch B d k z = 0
  | 0 => rfl
  | (_ + 1) => by simp [cost, hz]

theorem cost_succ {d : S → ℝ} {z : S} (hz : z ∉ B) (k : ℕ) :
    cost ch B d (k + 1) z = d z + ∑ y, ch.P z y * cost ch B d k y := by
  simp [cost, hz]

/-- The recursion satisfied by `E_z[σ_B ∧ K]` off the target set. -/
theorem partialHit_succ {z : S} (hz : z ∉ B) (k : ℕ) :
    partialHit ch B (k + 1) z = 1 + ∑ y, ch.P z y * partialHit ch B k y := by
  have h1 : partialHit ch B (k + 1) z
      = (∑ j ∈ range k, notHit ch B (j + 1) z) + notHit ch B 0 z := by
    simpa [partialHit] using Finset.sum_range_succ' (fun j => notHit ch B j z) k
  have h2 : ∀ j, notHit ch B (j + 1) z = ∑ y, ch.P z y * notHit ch B j y := by
    intro j; simp [notHit, hz]
  have h3 : (∑ j ∈ range k, notHit ch B (j + 1) z)
      = ∑ y, ch.P z y * partialHit ch B k y := by
    calc (∑ j ∈ range k, notHit ch B (j + 1) z)
        = ∑ j ∈ range k, ∑ y, ch.P z y * notHit ch B j y := by
          exact Finset.sum_congr rfl fun j _ => h2 j
      _ = ∑ y, ∑ j ∈ range k, ch.P z y * notHit ch B j y := Finset.sum_comm
      _ = ∑ y, ch.P z y * partialHit ch B k y := by
          exact Finset.sum_congr rfl fun y _ => by rw [partialHit, Finset.mul_sum]
  rw [h1, h3, notHit, if_neg hz]
  ring

/--
**The optional-stopping (Wald) step.**

If every visited state carries an expected cost at most `D`, then the expected
cost accumulated before hitting `B` is at most `D` times the expected hitting
time: `E_z[∑_{k<σ_B} d(Z_k)] ≤ D · E_z[σ_B ∧ K]` at every truncation level.
-/
theorem cost_le_mul_partialHit {d : S → ℝ} {D : ℝ} (hD : 0 ≤ D) (hdD : ∀ z, d z ≤ D) :
    ∀ (k : ℕ) (z : S), cost ch B d k z ≤ D * partialHit ch B k z := by
  intro k
  induction k with
  | zero => intro z; simp [cost, partialHit]
  | succ k ih =>
      intro z
      by_cases hz : z ∈ B
      · simp only [cost, hz, if_true]
        exact mul_nonneg hD (partialHit_nonneg ch B (k + 1) z)
      · have hsum : ∑ y, ch.P z y * cost ch B d k y
            ≤ ∑ y, ch.P z y * (D * partialHit ch B k y) :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (ih y) (ch.P_nonneg z y)
        have hrw : ∑ y, ch.P z y * (D * partialHit ch B k y)
            = D * ∑ y, ch.P z y * partialHit ch B k y := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
        simp only [cost, hz, if_false]
        rw [partialHit_succ ch B hz k]
        have := hdD z
        nlinarith [hsum, hrw]

theorem cost_nonneg {d : S → ℝ} (hd : ∀ z, 0 ≤ d z) : ∀ (k : ℕ) (z : S), 0 ≤ cost ch B d k z
  | 0, _ => le_rfl
  | (k + 1), z => by
      by_cases hz : z ∈ B
      · simp [cost_of_mem ch B hz]
      · rw [cost_succ ch B hz]
        have : 0 ≤ ∑ y, ch.P z y * cost ch B d k y :=
          sum_nonneg fun y _ => mul_nonneg (ch.P_nonneg z y) (cost_nonneg hd k y)
        linarith [hd z]

theorem cost_le_succ {d : S → ℝ} (hd : ∀ z, 0 ≤ d z) :
    ∀ (k : ℕ) (z : S), cost ch B d k z ≤ cost ch B d (k + 1) z
  | 0, z => cost_nonneg ch B hd 1 z
  | (k + 1), z => by
      by_cases hz : z ∈ B
      · simp [cost_of_mem ch B hz]
      · rw [cost_succ ch B hz, cost_succ ch B hz]
        have : ∑ y, ch.P z y * cost ch B d k y ≤ ∑ y, ch.P z y * cost ch B d (k + 1) y :=
          sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (cost_le_succ hd k y) (ch.P_nonneg z y)
        linarith

open Filter Topology in
/-- The truncated costs converge to the total accumulated cost. -/
theorem cost_tendsto {d : S → ℝ} (hd : ∀ z, 0 ≤ d z) {R : ℝ} {z : S}
    (hR : ∀ k, cost ch B d k z ≤ R) :
    Tendsto (fun k => cost ch B d k z) atTop (𝓝 (costLim ch B d z)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun k => cost_le_succ ch B hd k z)
    ⟨R, by rintro _ ⟨k, rfl⟩; exact hR k⟩

theorem costLim_nonneg {d : S → ℝ} (hd : ∀ z, 0 ≤ d z) {R : ℝ} {z : S}
    (hR : ∀ k, cost ch B d k z ≤ R) : 0 ≤ costLim ch B d z :=
  le_ciSup_of_le ⟨R, by rintro _ ⟨k, rfl⟩; exact hR k⟩ 0 (cost_nonneg ch B hd 0 z)

open Filter Topology in
/--
**The total accumulated cost is a supersolution.**
Off the target set, `costLim z ≥ d z + ∑_y Q(z,y) costLim y`.  This is what makes
the accumulated cost usable in the comparison argument for the original walk.
-/
theorem costLim_supersolution {d : S → ℝ} (hd : ∀ z, 0 ≤ d z) {R : ℝ}
    (hR : ∀ k y, cost ch B d k y ≤ R) {z : S} (hz : z ∉ B) :
    d z + ∑ y, ch.P z y * costLim ch B d y ≤ costLim ch B d z := by
  have hlim : Tendsto (fun k => d z + ∑ y, ch.P z y * cost ch B d k y) atTop
      (𝓝 (d z + ∑ y, ch.P z y * costLim ch B d y)) := by
    refine Tendsto.const_add _ (tendsto_finset_sum _ fun y _ => ?_)
    exact (cost_tendsto ch B hd (fun k => hR k y)).const_mul _
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
  have h1 : cost ch B d (k + 1) z = d z + ∑ y, ch.P z y * cost ch B d k y :=
    cost_succ ch B hz k
  have h2 : cost ch B d (k + 1) z ≤ costLim ch B d z :=
    le_ciSup_of_le ⟨R, by rintro _ ⟨j, rfl⟩; exact hR j z⟩ (k + 1) le_rfl
  linarith [h1 ▸ h2]

/--
**A supersolution bounds the expected hitting time.**
If `g ≥ 0` satisfies `g v ≥ 1 + ∑_u P(v,u) g u` off `B`, then `E_v[σ_B] ≤ g v`.
-/
theorem partialHit_le_of_supersolution {g : S → ℝ} (hg0 : ∀ v, 0 ≤ g v)
    (hgs : ∀ v ∉ B, 1 + ∑ u, ch.P v u * g u ≤ g v) :
    ∀ (K : ℕ) (v : S), partialHit ch B K v ≤ g v := by
  intro K
  induction K with
  | zero => intro v; simpa [partialHit] using hg0 v
  | succ K ih =>
      intro v
      by_cases hv : v ∈ B
      · have : partialHit ch B (K + 1) v = 0 := by
          simp [partialHit, notHit_of_mem ch B hv]
        rw [this]; exact hg0 v
      · rw [partialHit_succ ch B hv]
        have hsum : ∑ u, ch.P v u * partialHit ch B K u ≤ ∑ u, ch.P v u * g u :=
          sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (ih u) (ch.P_nonneg v u)
        linarith [hgs v hv]

/-- The expected hitting time is bounded by any supersolution. -/
theorem hitTime_le_of_supersolution {g : S → ℝ} (hg0 : ∀ v, 0 ≤ g v)
    (hgs : ∀ v ∉ B, 1 + ∑ u, ch.P v u * g u ≤ g v) (v : S) :
    hitTime ch B v ≤ g v :=
  ciSup_le fun K => partialHit_le_of_supersolution ch B hg0 hgs K v

theorem hitTime_nonneg {R : ℝ} {v : S} (hR : ∀ K, partialHit ch B K v ≤ R) :
    0 ≤ hitTime ch B v :=
  le_ciSup_of_le ⟨R, by rintro _ ⟨K, rfl⟩; exact hR K⟩ 0 (le_of_eq (by simp [partialHit]))

theorem hitTime_of_mem {v : S} (hv : v ∈ B) : hitTime ch B v = 0 := by
  have : ∀ K : ℕ, partialHit ch B K v = 0 := fun K => by
    simp [partialHit, notHit_of_mem ch B hv]
  simp [hitTime, this]

open Filter Topology in
/-- The truncated expected hitting times converge to the expected hitting
time. -/
theorem partialHit_tendsto {R : ℝ} {v : S} (hR : ∀ K, partialHit ch B K v ≤ R) :
    Tendsto (fun K => partialHit ch B K v) atTop (𝓝 (hitTime ch B v)) :=
  tendsto_atTop_ciSup (monotone_nat_of_le_succ fun K =>
      partialHit_mono ch B (Nat.le_succ K) v)
    ⟨R, by rintro _ ⟨K, rfl⟩; exact hR K⟩

open Filter Topology in
/-- The first-step recursion for the expected hitting time. -/
theorem hitTime_succ {R : ℝ} (hR : ∀ K u, partialHit ch B K u ≤ R) {v : S} (hv : v ∉ B) :
    hitTime ch B v = 1 + ∑ u, ch.P v u * hitTime ch B u := by
  have h1 : Tendsto (fun K => partialHit ch B (K + 1) v) atTop (𝓝 (hitTime ch B v)) :=
    (partialHit_tendsto ch B (fun K => hR K v)).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun K => 1 + ∑ u, ch.P v u * partialHit ch B K u) atTop
      (𝓝 (1 + ∑ u, ch.P v u * hitTime ch B u)) := by
    refine Tendsto.const_add _ (tendsto_finset_sum _ fun u _ => ?_)
    exact (partialHit_tendsto ch B (fun K => hR K u)).const_mul _
  refine tendsto_nhds_unique h1 ?_
  simpa [partialHit_succ ch B hv] using h2

/--
**Expected accumulated cost, final form.**
If every state costs at most `D ≥ 0` and the expected hitting time of `B` is at
most `R`, the total expected accumulated cost is at most `D · R`.
-/
theorem costLim_le {d : S → ℝ} {D R : ℝ} (hD : 0 ≤ D) (hdD : ∀ z, d z ≤ D) {z : S}
    (hR : ∀ K : ℕ, partialHit ch B K z ≤ R) :
    costLim ch B d z ≤ D * R := by
  refine ciSup_le fun k => ?_
  exact le_trans (cost_le_mul_partialHit ch B hD hdD k z)
    (mul_le_mul_of_nonneg_left (hR k) hD)

end Cost

section Recursion

/--
**Lemma 3.11, the recursion `T_s ≤ T_{s-1} + C_R C_⋆ q^{s-1}`.**

The hypotheses are exactly the paper's inputs:

* `hskel`: from any starting point the expected hitting time of the level-one
  skeleton is at most `Tprev = T_{s-1}` (a level-one cell is an
  `(s-1)`-step copy);
* `hdecomp`: the exit time decomposes as "time to reach the skeleton" plus the
  time accumulated by the watched chain (this is the identification of the
  watched process with the conductance walk on the rule graph, Lemma 2.4);
* the watched chain is the conductance walk with conductances in `[a, b]`
  (Corollary 2.8: a fixed compact subset of `(0,∞)^K`), and the rule graph is
  connected to the pair of terminals `B` within `N` steps (`nu`);
* `hd`: each jump lasts at most `Cstar * q^s` in expectation (Lemma 2.22
  applied inside the copy with parameter `s-1`).

The conclusion is the paper's display, with the explicit constant
`C_R = N (card S · b / a)^N`.
-/
theorem watched_chain_recursion
    (c : S → S → ℝ) (hc : ∀ z y, 0 ≤ c z y) (hpos : ∀ z, 0 < ∑ y, c z y)
    (B : Finset S) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (hcb : ∀ z y, c z y ≤ b) (nu : S → ℕ) {N : ℕ} (hN : 1 ≤ N) (hnu : ∀ z, nu z ≤ N)
    (hdesc : ∀ z, z ∉ B → ∃ y, a ≤ c z y ∧ nu y < nu z)
    (d : S → ℝ) {Cstar q : ℝ} (hCstar : 0 ≤ Cstar) (hq : 0 < q) (s : ℕ)
    (hd : ∀ z, d z ≤ Cstar * q ^ s)
    (Texit Tprev : ℝ) (z : S)
    (hdecomp : Texit ≤ Tprev + costLim (condChain c hc hpos) B d z) :
    Texit ≤ Tprev
      + ((N : ℝ) / (a / (Fintype.card S * b)) ^ N) * (Cstar * q ^ s) := by
  set ch := condChain c hc hpos with hch
  set CR : ℝ := (N : ℝ) / (a / (Fintype.card S * b)) ^ N with hCR
  have hcard : 0 < (Fintype.card S : ℝ) := by
    have : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨z⟩
    exact_mod_cast this
  have hpart : ∀ K : ℕ, partialHit ch B K z ≤ CR :=
    condChain_partialHit_le c hc hpos B ha hb hab hcb nu hN hnu hdesc z
  have hcost : costLim ch B d z ≤ (Cstar * q ^ s) * CR :=
    costLim_le ch B (by positivity) hd hpart
  have : CR * (Cstar * q ^ s) = (Cstar * q ^ s) * CR := by ring
  linarith

/--
**Lemma 3.11, "uniform exit bound for cells".**
Once the recursion is available for every `s`, unrolling it (as in
`geometric_recursion_bound`) gives `T_s ≤ C_T q^s` with
`C_T = T_0 + C_R C_⋆/(q-1)`.
-/
theorem watched_chain_exit_bound (T : ℕ → ℝ) {q CR Cstar : ℝ} (hq : 1 < q)
    (hCR : 0 ≤ CR) (hCstar : 0 ≤ Cstar) (h0 : 0 ≤ T 0)
    (hrec : ∀ s : ℕ, T (s + 1) ≤ T s + CR * (Cstar * q ^ s)) :
    ∀ s : ℕ, T s ≤ (T 0 + CR * Cstar / (q - 1)) * q ^ s := by
  refine geometric_recursion_bound T q (CR * Cstar) hq (mul_nonneg hCR hCstar) h0 ?_
  intro s
  have := hrec s
  nlinarith [this]

/--
**Lemma 3.11, uniform exit bound for cells, end to end.**

The rule graph `S` and its pair of terminals `B` are fixed; only the traced
conductances `c s` change with the number `s` of substitution steps, and they
stay in the compact range `[a, b]` (Corollary 2.8).  Given

* connectivity of the rule graph to the terminals within `N` steps (`nu`),
* the one-jump time bound `d s z ≤ C_⋆ q^s` (Lemma 2.22, `q = ρ(M)ρ(Ψ) > 1`),
* and the decomposition of the exit time of an `(s+1)`-step copy into the time
  to reach the level-one skeleton (`≤ T_s`) plus the time accumulated by the
  watched chain (Lemma 2.4),

one gets `T_s ≤ C_T q^s` with the completely explicit constant
`C_T = T_0 + C_R C_⋆/(q-1)` and `C_R = N (card S · b / a)^N`.
-/
theorem cell_exit_time_bound
    (B : Finset S) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (nu : S → ℕ) {N : ℕ} (hN : 1 ≤ N) (hnu : ∀ z, nu z ≤ N)
    (c : ℕ → S → S → ℝ) (hc : ∀ s z y, 0 ≤ c s z y) (hpos : ∀ s z, 0 < ∑ y, c s z y)
    (hcb : ∀ s z y, c s z y ≤ b)
    (hdesc : ∀ s z, z ∉ B → ∃ y, a ≤ c s z y ∧ nu y < nu z)
    (d : ℕ → S → ℝ) {Cstar q : ℝ} (hCstar : 0 ≤ Cstar) (hq : 1 < q)
    (hd : ∀ s z, d s z ≤ Cstar * q ^ s)
    (T : ℕ → ℝ) (h0 : 0 ≤ T 0)
    (hdecomp : ∀ s, ∃ z,
      T (s + 1) ≤ T s + costLim (condChain (c s) (hc s) (hpos s)) B (d s) z) :
    ∀ s : ℕ, T s
      ≤ (T 0 + ((N : ℝ) / (a / (Fintype.card S * b)) ^ N) * Cstar / (q - 1)) * q ^ s := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  set CR : ℝ := (N : ℝ) / (a / (Fintype.card S * b)) ^ N with hCR
  have hCR0 : 0 ≤ CR := by
    have hbase : 0 ≤ a / ((Fintype.card S : ℝ) * b) := div_nonneg ha.le (by positivity)
    exact div_nonneg (Nat.cast_nonneg N) (pow_nonneg hbase N)
  refine watched_chain_exit_bound T hq hCR0 hCstar h0 ?_
  intro s
  obtain ⟨z, hz⟩ := hdecomp s
  exact watched_chain_recursion (c s) (hc s) (hpos s) B ha hb hab (hcb s) nu hN hnu
    (hdesc s) (d s) hCstar hq0 s (hd s) (T (s + 1)) (T s) z hz

end Recursion

end IGS.Sec31
