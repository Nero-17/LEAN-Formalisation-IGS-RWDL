import RequestProject.Section31.TraceChain

/-!
# The excursion decomposition of the exit time

Reference: arXiv:2603.13798, §3.1, proof of Lemma 3.11, paragraph "Uniform exit
bound for cells":

> From any `z`, the hitting time of the level-one skeleton `V_1(H)` is bounded
> by `σ_{∂Λ'}` for the level-one cell `Λ'` containing `z`, hence its expectation
> is at most `T_{s-1}`.  Observed at successive distinct skeleton vertices, the
> walk is the random walk on the rule graph … the expected number of skeleton
> jumps before hitting the two terminals of `H` is at most a constant `C_R` …
> Each jump … lasts at most `C_⋆ (ρ(M)ρ(Ψ))^{s-1}` in expectation … Optional
> stopping then gives `T_s ≤ T_{s-1} + C_R C_⋆ (ρ(M)ρ(Ψ))^{s-1}`.

`exit_time_le_skeleton_add_cost` is exactly that display, *proved* for a finite
Markov chain: no strong Markov property is assumed, the decomposition being
obtained by exhibiting

  `g(v) = E_v[σ_S] + ∑_w P_v(X_{σ_S} = w) · (accumulated jump time from w)`

as a supersolution of the hitting-time equation for the terminals `B`.  The
three ingredients are the ones the paper names: the bound `T_{s-1}` on the time
to reach the skeleton (`hRS`), the bound `C_⋆ q^{s-1}` on one excursion (`hd`,
Lemma 2.22) and the bound `C_R` on the number of watched jumps (`hQ`, which
`WatchedChain.condChain_partialHit_le` supplies from the compact family of
traced conductances, Corollary 2.8).
-/

namespace IGS.Sec31

open Finset Filter Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two terminals, viewed as a subset of the skeleton. -/
def termIn (S B : Finset V) : Finset {x // x ∈ S} :=
  S.attach.filter fun w => (w : V) ∈ B

omit [Fintype V] in
@[simp] theorem mem_termIn {S B : Finset V} (w : {x // x ∈ S}) :
    w ∈ termIn S B ↔ (w : V) ∈ B := by
  simp [termIn]

/-- The expected duration of one excursion of the walk away from the skeleton:
one step, then the return to the skeleton. -/
noncomputable def excursionTime (ch : FinChain V) (S : Finset V) (w : {x // x ∈ S}) : ℝ :=
  1 + ∑ u, ch.P (w : V) u * hitTime ch S u

/--
**Optional stopping / excursion decomposition (Lemma 3.11).**

For a finite Markov chain with skeleton `S` and terminals `B`:

* `hRS` — the expected time to reach the skeleton is at most `R_S` (`= T_{s-1}`);
* `hd` — one excursion lasts at most `D` in expectation (`= C_⋆ q^{s-1}`);
* `hQ` — the watched chain on the skeleton hits the terminals within `C_R`
  jumps in expectation;

then the expected time for the walk to reach the terminals is at most
`R_S + D · C_R`.
-/
theorem exit_time_le_skeleton_add_cost
    (ch : FinChain V) (S B : Finset V)
    (hS : ∀ v, Tendsto (fun k => notHit ch S k v) atTop (𝓝 0))
    {RS : ℝ} (hRS : ∀ (K : ℕ) (v : V), partialHit ch S K v ≤ RS)
    {D CR : ℝ} (hD : 0 ≤ D) (hCR : 0 ≤ CR)
    (hd : ∀ w : {x // x ∈ S}, excursionTime ch S w ≤ D)
    (hQ : ∀ (K : ℕ) (w : {x // x ∈ S}),
      partialHit (traceChain ch S hS) (termIn S B) K w ≤ CR)
    (z : V) :
    hitTime ch B z ≤ RS + D * CR := by
  classical
  set Q := traceChain ch S hS with hQdef
  set B' := termIn S B with hB'
  set d' := excursionTime ch S with hd'
  have hQP : ∀ (v' y : {x // x ∈ S}),
      Q.P v' y = ∑ u, ch.P (v' : V) u * hitDistLim ch S u (y : V) := fun _ _ => rfl
  -- the accumulated jump time of the watched chain, extended by `0` off the skeleton
  set h : V → ℝ := fun v => if hv : v ∈ S then costLim Q B' d' ⟨v, hv⟩ else 0 with hh
  have hitTimeS_nonneg : ∀ v, 0 ≤ hitTime ch S v := fun v =>
    hitTime_nonneg ch S (fun K => hRS K v)
  have hd'0 : ∀ w : {x // x ∈ S}, 0 ≤ d' w := by
    intro w
    have hsum : 0 ≤ ∑ u, ch.P (w : V) u * hitTime ch S u :=
      sum_nonneg fun u _ => mul_nonneg (ch.P_nonneg _ u) (hitTimeS_nonneg u)
    simp only [hd', excursionTime]
    linarith
  have hcost : ∀ (k : ℕ) (w : {x // x ∈ S}), cost Q B' d' k w ≤ D * CR := fun k w =>
    le_trans (cost_le_mul_partialHit Q B' hD hd k w)
      (mul_le_mul_of_nonneg_left (hQ k w) hD)
  have hDCR : 0 ≤ D * CR := mul_nonneg hD hCR
  have hh0 : ∀ v, 0 ≤ h v := by
    intro v
    simp only [hh]
    split
    · exact costLim_nonneg Q B' hd'0 (fun k => hcost k _)
    · exact le_rfl
  have hhle : ∀ v, h v ≤ D * CR := by
    intro v
    simp only [hh]
    split
    · exact costLim_le Q B' hD hd (fun K => hQ K _)
    · exact hDCR
  have hh_mem : ∀ w : {x // x ∈ S}, h (w : V) = costLim Q B' d' w := by
    intro w
    simp only [hh, dif_pos w.2]
  have hh_not_mem : ∀ {w : V}, w ∉ S → h w = 0 := by
    intro w hw
    simp only [hh, dif_neg hw]
  -- restricting a sum over the state space to the skeleton
  have hrestrict : ∀ u : V, ∑ y : {x // x ∈ S}, hitDistLim ch S u (y : V) * h (y : V)
      = ∑ w, hitDistLim ch S u w * h w := by
    intro u
    have h1 : ∑ y : {x // x ∈ S}, hitDistLim ch S u (y : V) * h (y : V)
        = ∑ w ∈ S, hitDistLim ch S u w * h w :=
      Finset.sum_coe_sort S fun w => hitDistLim ch S u w * h w
    rw [h1]
    refine Finset.sum_subset (Finset.subset_univ S) ?_
    intro w _ hw
    rw [hh_not_mem hw]; ring
  -- the candidate supersolution
  set g : V → ℝ := fun v => hitTime ch S v + ∑ w, hitDistLim ch S v w * h w with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v =>
    add_nonneg (hitTimeS_nonneg v)
      (sum_nonneg fun w _ => mul_nonneg (hitDistLim_nonneg ch S v w) (hh0 w))
  have hswap : ∀ v ∉ S, ∑ w, hitDistLim ch S v w * h w
      = ∑ u, ch.P v u * ∑ w, hitDistLim ch S u w * h w := by
    intro v hv
    calc ∑ w, hitDistLim ch S v w * h w
        = ∑ w, (∑ u, ch.P v u * hitDistLim ch S u w) * h w := by
          exact sum_congr rfl fun w _ => by rw [hitDistLim_succ ch S hv w]
      _ = ∑ w, ∑ u, ch.P v u * (hitDistLim ch S u w * h w) := by
          refine sum_congr rfl fun w _ => ?_
          rw [Finset.sum_mul]
          exact sum_congr rfl fun u _ => by ring
      _ = ∑ u, ∑ w, ch.P v u * (hitDistLim ch S u w * h w) := Finset.sum_comm
      _ = ∑ u, ch.P v u * ∑ w, hitDistLim ch S u w * h w :=
          sum_congr rfl fun u _ => by rw [Finset.mul_sum]
  have hsuper : ∀ v ∉ B, 1 + ∑ u, ch.P v u * g u ≤ g v := by
    intro v hvB
    by_cases hv : v ∈ S
    · -- a skeleton point: this is the supersolution property of the watched chain
      set v' : {x // x ∈ S} := ⟨v, hv⟩ with hv'
      have hv'B : v' ∉ B' := by simp [hB', hv', hvB]
      have hgv : g v = h v := by
        have hdirac : ∑ w, hitDistLim ch S v w * h w = h v := by
          simp [hitDistLim_of_mem ch S hv]
        simp only [hg, hitTime_of_mem ch S hv, hdirac, zero_add]
      have hgu : ∑ u, ch.P v u * g u
          = (∑ u, ch.P v u * hitTime ch S u)
            + ∑ u, ch.P v u * ∑ w, hitDistLim ch S u w * h w := by
        rw [← Finset.sum_add_distrib]
        exact sum_congr rfl fun u _ => by simp only [hg]; ring
      have hQsum : ∑ y : {x // x ∈ S}, Q.P v' y * costLim Q B' d' y
          = ∑ u, ch.P v u * ∑ w, hitDistLim ch S u w * h w := by
        calc ∑ y : {x // x ∈ S}, Q.P v' y * costLim Q B' d' y
            = ∑ y : {x // x ∈ S},
                (∑ u, ch.P v u * hitDistLim ch S u (y : V)) * h (y : V) := by
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [hQP v' y, hh_mem y]
          _ = ∑ y : {x // x ∈ S}, ∑ u,
                ch.P v u * (hitDistLim ch S u (y : V) * h (y : V)) := by
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [Finset.sum_mul]
              exact sum_congr rfl fun u _ => by ring
          _ = ∑ u, ∑ y : {x // x ∈ S},
                ch.P v u * (hitDistLim ch S u (y : V) * h (y : V)) := Finset.sum_comm
          _ = ∑ u, ch.P v u * ∑ w, hitDistLim ch S u w * h w := by
              refine sum_congr rfl fun u _ => ?_
              rw [← Finset.mul_sum, hrestrict u]
      have hsuperQ := costLim_supersolution Q B' hd'0 hcost hv'B
      rw [hQsum] at hsuperQ
      have hd'v : d' v' = 1 + ∑ u, ch.P v u * hitTime ch S u := rfl
      rw [hgv, hh_mem v', hgu]
      rw [hd'v] at hsuperQ
      linarith
    · -- off the skeleton: the first-step recursion, with equality
      have h1 : hitTime ch S v = 1 + ∑ u, ch.P v u * hitTime ch S u :=
        hitTime_succ ch S (fun K u => hRS K u) hv
      have h2 : ∑ u, ch.P v u * g u
          = (∑ u, ch.P v u * hitTime ch S u)
            + ∑ u, ch.P v u * ∑ w, hitDistLim ch S u w * h w := by
        rw [← Finset.sum_add_distrib]
        exact sum_congr rfl fun u _ => by simp only [hg]; ring
      have h3 := hswap v hv
      simp only [hg]
      rw [h1, h2, h3]
      linarith
  -- conclusion
  have hmain : hitTime ch B z ≤ g z := hitTime_le_of_supersolution ch B hg0 hsuper z
  have hgz : g z ≤ RS + D * CR := by
    have hA : hitTime ch S z ≤ RS := ciSup_le fun K => hRS K z
    have hB2 : ∑ w, hitDistLim ch S z w * h w ≤ D * CR := by
      calc ∑ w, hitDistLim ch S z w * h w
          ≤ ∑ w, hitDistLim ch S z w * (D * CR) :=
            sum_le_sum fun w _ =>
              mul_le_mul_of_nonneg_left (hhle w) (hitDistLim_nonneg ch S z w)
        _ = (∑ w, hitDistLim ch S z w) * (D * CR) := by rw [Finset.sum_mul]
        _ ≤ 1 * (D * CR) := mul_le_mul_of_nonneg_right (hitDistLim_sum_le_one ch S z) hDCR
        _ = D * CR := one_mul _
    simp only [hg]
    linarith
  linarith

/--
**Lemma 3.11, the recursion `T_s ≤ T_{s-1} + C_R C_⋆ q^{s-1}`, with the
decomposition proved.**

The only remaining input from §2 is `hQcond`: the identification of the watched
chain with the conductance walk on the rule graph whose colour-`j` conductances
are the effective conductances of the `(s-1)`-step copies (Lemma 2.4), those
conductances lying in a fixed compact range `[a,b]` (Corollary 2.8).  The bound
`C_⋆ q^{s-1}` on one excursion is Lemma 2.22 (`hd`), and `T_{s-1}` bounds the
time to reach the level-one skeleton (`hRS`).  Everything else — the expected
number of jumps and the optional-stopping composition — is proved.

Feeding the resulting recursion into `watched_chain_exit_bound` (equivalently
`geometric_recursion_bound`) yields the paper's `T_s ≤ C_T (ρ(M)ρ(Ψ))^s`.
-/
theorem cell_exit_recursion_of_conductance_skeleton
    (ch : FinChain V) (S B : Finset V)
    (hS : ∀ v, Tendsto (fun k => notHit ch S k v) atTop (𝓝 0))
    {RS : ℝ} (hRS : ∀ (K : ℕ) (v : V), partialHit ch S K v ≤ RS)
    (c : {x // x ∈ S} → {x // x ∈ S} → ℝ) (hc : ∀ z y, 0 ≤ c z y)
    (hpos : ∀ z, 0 < ∑ y, c z y)
    (hQcond : traceChain ch S hS = condChain c hc hpos)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hcb : ∀ z y, c z y ≤ b)
    (nu : {x // x ∈ S} → ℕ) {N : ℕ} (hN : 1 ≤ N) (hnu : ∀ z, nu z ≤ N)
    (hdesc : ∀ z, z ∉ termIn S B → ∃ y, a ≤ c z y ∧ nu y < nu z)
    {Dstep : ℝ} (hD : 0 ≤ Dstep) (hd : ∀ w : {x // x ∈ S}, excursionTime ch S w ≤ Dstep)
    (z : V) :
    hitTime ch B z
      ≤ RS + Dstep * ((N : ℝ) / (a / (Fintype.card {x // x ∈ S} * b)) ^ N) := by
  set CR : ℝ := (N : ℝ) / (a / (Fintype.card {x // x ∈ S} * b)) ^ N with hCRdef
  have hCR0 : 0 ≤ CR := by
    have hbase : 0 ≤ a / ((Fintype.card {x // x ∈ S} : ℝ) * b) := div_nonneg ha.le (by positivity)
    exact div_nonneg (Nat.cast_nonneg N) (pow_nonneg hbase N)
  refine exit_time_le_skeleton_add_cost ch S B hS hRS hD hCR0 hd ?_ z
  intro K w
  rw [hQcond]
  exact condChain_partialHit_le c hc hpos (termIn S B) ha hb hab hcb nu hN hnu hdesc w K

end IGS.Sec31
