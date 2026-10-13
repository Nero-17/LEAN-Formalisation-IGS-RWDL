import RequestProject.Section31.DirichletPrinciple

/-!
# §3.1: the oscillation contraction of Lemma `sec31_continuous_harmonics`

Reference: arXiv:2603.13798, §3.1, Lemma `lem:sec31_continuous_harmonics`.

The proof of that lemma rests on one geometric fact about a *single* rule graph:

> for every rule graph and every admissible conductance vector, the `0`–`1`
> harmonic profile has **edge oscillation strictly smaller than `1`**.

In `SECTION31_NOTES.md` this was the one point flagged as needing an extra
hypothesis, because an edge joining the two planting vertices directly (a
"shortcut edge") would carry oscillation exactly `1`.  Under the standing
assumption of the paper (Assumption `ass:standing`: distance-positivity, plus
`d(β_1^+,β_1^-) ≥ 2` when `K = 1`) shortcut edges do not exist — this is proved
combinatorially in `RequestProject/Section31/NoShortcut.lean` — and this file
turns that combinatorial fact into the analytic statement, from scratch:

* `grad_eq_zero_of_min` — a minimiser of the energy is harmonic at every
  interior vertex (the Euler–Lagrange equation, obtained by differentiating the
  energy along `g + t δ_x`);
* `range_subset_of_min` — the maximum principle `0 ≤ g ≤ 1`, obtained by
  truncation: clamping decreases the energy, and the minimiser is unique;
* `grad_lt_zero_of_zero_at` — the strong maximum principle at a vertex where a
  nonnegative function vanishes but has a neighbour with a positive value;
* `mem_of_osc_one` — consequently an edge of oscillation exactly `1` must join
  two *boundary* vertices;
* `edge_osc_lt_one_of_no_shortcut` — **the statement used by the paper**: with no
  shortcut edge, every edge oscillation of the `0`–`1` profile is `< 1`;
* `energy_affine`, `min_affine`, `edge_osc_le_mul_of_profile` — the affine
  dependence of the minimiser on its boundary data, which converts the previous
  bound into the contraction "child-cell oscillation `≤ θ ·` parent-cell
  oscillation" used in the geometric decay `osc_n ≤ θ^n osc_0`.
-/

namespace IGS.Sec31

namespace FiniteNetwork

open Finset

variable {V : Type*} [DecidableEq V] (net : FiniteNetwork V)

/-- The signed incidence of the edge `e` at the vertex `x`. -/
def inc (e : net.Edge) (x : V) : ℝ :=
  (if (net.ends e).1 = x then (1 : ℝ) else 0) - (if (net.ends e).2 = x then (1 : ℝ) else 0)

/-- Half the derivative of the energy at `g` in the direction of the unit spike at `x`:
`grad g x = ∑_e c_e · inc(e,x) · (g(a_e) - g(b_e))`.  A function is *harmonic* at `x`
when this vanishes. -/
noncomputable def grad (g : V → ℝ) (x : V) : ℝ :=
  ∑ e, net.cond e * net.inc e x * (g (net.ends e).1 - g (net.ends e).2)

/-- The energy along the line `g + t·δ_x` is the quadratic
`ℰ(g) + 2t·grad g x + t²·∑_e c_e inc(e,x)²`. -/
theorem energy_perturb (g : V → ℝ) (x : V) (t : ℝ) :
    net.energy (fun y => g y + if y = x then t else 0)
      = net.energy g + 2 * t * net.grad g x
        + t ^ 2 * ∑ e, net.cond e * (net.inc e x) ^ 2 := by
  unfold energy grad
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h : (g (net.ends e).1 + (if (net.ends e).1 = x then t else 0))
      - (g (net.ends e).2 + (if (net.ends e).2 = x then t else 0))
      = (g (net.ends e).1 - g (net.ends e).2) + t * net.inc e x := by
    unfold inc; split_ifs <;> ring
  rw [h]; ring

omit [DecidableEq V] in
/-- If the quadratic `t ↦ 2tb + t²A` with `A ≥ 0` is nonnegative for all `t`, then `b = 0`. -/
theorem eq_zero_of_quadratic_nonneg (b A : ℝ) (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * A) : b = 0 := by
  have hA1 : (0 : ℝ) < A + 1 := by linarith
  have key := h (-(b / (A + 1)))
  have hexp : 2 * (-(b / (A + 1))) * b + (-(b / (A + 1))) ^ 2 * A
      = -(b ^ 2 * (A + 2)) / (A + 1) ^ 2 := by
    field_simp; ring
  rw [hexp] at key
  have h2 : 0 ≤ -(b ^ 2 * (A + 2)) := by
    have hsq : (0 : ℝ) < (A + 1) ^ 2 := by positivity
    have := (le_div_iff₀ hsq).1 key
    linarith
  nlinarith [sq_nonneg b]

/--
**The Euler–Lagrange equation.**  A minimiser of the energy among the functions
with prescribed values on `V₀` is harmonic at every vertex outside `V₀`.
-/
theorem grad_eq_zero_of_min (V₀ : Finset V) (h g : V → ℝ)
    (hmin : ∀ f, (∀ y ∈ V₀, f y = h y) → net.energy g ≤ net.energy f)
    (hbd : ∀ y ∈ V₀, g y = h y) (x : V) (hx : x ∉ V₀) : net.grad g x = 0 := by
  have hA : 0 ≤ ∑ e, net.cond e * (net.inc e x) ^ 2 :=
    Finset.sum_nonneg fun e _ => by have := (net.cond_pos e).le; positivity
  refine eq_zero_of_quadratic_nonneg _ _ hA fun t => ?_
  have hadm : ∀ y ∈ V₀, (fun y => g y + if y = x then t else 0) y = h y := by
    intro y hy
    have : y ≠ x := fun hyx => hx (hyx ▸ hy)
    simp [this, hbd y hy]
  have := hmin _ hadm
  rw [net.energy_perturb g x t] at this
  linarith

/-- `grad` changes sign under `g ↦ c - g`; in particular harmonicity is preserved. -/
theorem grad_const_sub (g : V → ℝ) (c : ℝ) (x : V) :
    net.grad (fun y => c - g y) x = -net.grad g x := by
  unfold grad
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

/--
**Strong maximum principle.**  If `g ≥ 0`, `g x = 0`, and some edge joins `x` to a
vertex where `g` is positive, then `grad g x < 0`; in particular `g` is not
harmonic at `x`.
-/
theorem grad_lt_zero_of_zero_at (g : V → ℝ) (x : V) (hnn : ∀ y, 0 ≤ g y) (hx : g x = 0)
    (e₀ : net.Edge)
    (h₀ : ((net.ends e₀).1 = x ∧ 0 < g (net.ends e₀).2)
        ∨ ((net.ends e₀).2 = x ∧ 0 < g (net.ends e₀).1)) :
    net.grad g x < 0 := by
  have hle : ∀ e ∈ (univ : Finset net.Edge),
      net.cond e * net.inc e x * (g (net.ends e).1 - g (net.ends e).2) ≤ 0 := by
    intro e _
    have hc := (net.cond_pos e).le
    by_cases h1 : (net.ends e).1 = x <;> by_cases h2 : (net.ends e).2 = x
    · simp [inc, h1, h2]
    · have : g (net.ends e).1 = 0 := by rw [h1, hx]
      have hq := hnn (net.ends e).2
      simp only [inc, h1, h2, if_true, if_false, sub_zero, mul_one]
      nlinarith
    · have : g (net.ends e).2 = 0 := by rw [h2, hx]
      have hp := hnn (net.ends e).1
      simp only [inc, h1, h2, if_true, if_false, zero_sub]
      nlinarith
    · simp [inc, h1, h2]
  have hlt : ∃ e ∈ (univ : Finset net.Edge),
      net.cond e * net.inc e x * (g (net.ends e).1 - g (net.ends e).2) < 0 := by
    refine ⟨e₀, Finset.mem_univ _, ?_⟩
    have hc := net.cond_pos e₀
    rcases h₀ with ⟨h1, hpos⟩ | ⟨h2, hpos⟩
    · have hzero : g (net.ends e₀).1 = 0 := by rw [h1, hx]
      have h2 : (net.ends e₀).2 ≠ x := by
        intro hcon; rw [hcon, hx] at hpos; exact lt_irrefl 0 hpos
      simp only [inc, h1, h2, if_true, if_false, sub_zero, mul_one]
      nlinarith
    · have hzero : g (net.ends e₀).2 = 0 := by rw [h2, hx]
      have h1 : (net.ends e₀).1 ≠ x := by
        intro hcon; rw [hcon, hx] at hpos; exact lt_irrefl 0 hpos
      simp only [inc, h1, h2, if_true, if_false, zero_sub]
      nlinarith
  have := Finset.sum_lt_sum hle hlt
  simpa [grad] using this

/-- The clamp to `[0,1]`. -/
noncomputable def clamp (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp_nonneg (t : ℝ) : 0 ≤ clamp t := le_max_left _ _

theorem clamp_le_one (t : ℝ) : clamp t ≤ 1 := max_le (by norm_num) (min_le_left _ _)

theorem clamp_eq_self {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : clamp t = t := by
  unfold clamp; rw [min_eq_right h1, max_eq_right h0]

/-- Clamping is `1`-Lipschitz, in squared form. -/
theorem clamp_sq_le (s t : ℝ) : (clamp s - clamp t) ^ 2 ≤ (s - t) ^ 2 := by
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> nlinarith

omit [DecidableEq V] in
/-- Clamping decreases the energy. -/
theorem energy_clamp_le (g : V → ℝ) : net.energy (fun y => clamp (g y)) ≤ net.energy g :=
  Finset.sum_le_sum fun e _ =>
    mul_le_mul_of_nonneg_left (clamp_sq_le _ _) (net.cond_pos e).le

omit [DecidableEq V] in
/--
**The maximum principle for the minimiser.**  If the boundary data take values in
`[0,1]`, then so does the (unique) energy minimiser.  The proof is truncation:
the clamped function is admissible and has no larger energy, hence is also a
minimiser, hence equals `g` by uniqueness.
-/
theorem range_subset_of_min (V₀ : Finset V) (h : V → ℝ) (K : ℝ)
    (hP : ∀ g : V → ℝ, (∀ x ∈ V₀, g x = 0) → ∀ x, (g x) ^ 2 ≤ K * net.energy g)
    (hh : ∀ x ∈ V₀, 0 ≤ h x ∧ h x ≤ 1) (g : V → ℝ) (hbd : ∀ x ∈ V₀, g x = h x)
    (hmin : ∀ f, (∀ x ∈ V₀, f x = h x) → net.energy g ≤ net.energy f) :
    ∀ x, 0 ≤ g x ∧ g x ≤ 1 := by
  set g' : V → ℝ := fun y => clamp (g y) with hg'
  have hbd' : ∀ x ∈ V₀, g' x = h x := by
    intro x hx
    have := hh x hx
    rw [hg']
    simp only
    rw [hbd x hx, clamp_eq_self this.1 this.2]
  have hle : net.energy g' ≤ net.energy g := net.energy_clamp_le g
  have hmin' : ∀ f, (∀ x ∈ V₀, f x = h x) → net.energy g' ≤ net.energy f := fun f hf =>
    le_trans hle (hmin f hf)
  have : g = g' := net.min_unique V₀ h K hP g g' hbd hbd' hmin hmin'
  intro x
  rw [this]
  exact ⟨clamp_nonneg _, clamp_le_one _⟩

/--
An edge whose oscillation for a harmonic `[0,1]`-valued function equals `1` must
have **both** endpoints on the boundary `V₀`.
-/
theorem mem_of_osc_one (V₀ : Finset V) (g : V → ℝ)
    (hharm : ∀ x, x ∉ V₀ → net.grad g x = 0)
    (hnn : ∀ y, 0 ≤ g y) (hub : ∀ y, g y ≤ 1) (e : net.Edge)
    (hosc : |g (net.ends e).1 - g (net.ends e).2| = 1) :
    (net.ends e).1 ∈ V₀ ∧ (net.ends e).2 ∈ V₀ := by
  -- the "zero endpoint" is on the boundary
  have hzero : ∀ (x y : V), g x = 0 → 0 < g y →
      (((net.ends e).1 = x ∧ (net.ends e).2 = y) ∨ ((net.ends e).2 = x ∧ (net.ends e).1 = y)) →
      x ∈ V₀ := by
    intro x y hx hy he
    by_contra hxV
    have h0 := hharm x hxV
    have hneg : net.grad g x < 0 := by
      refine net.grad_lt_zero_of_zero_at g x hnn hx e ?_
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, by rw [h2]; exact hy⟩
      · exact Or.inr ⟨h1, by rw [h2]; exact hy⟩
    rw [h0] at hneg
    exact lt_irrefl 0 hneg
  -- the "one endpoint" is on the boundary: apply the same to `1 - g`
  have hone : ∀ (x y : V), g x = 1 → g y < 1 →
      (((net.ends e).1 = x ∧ (net.ends e).2 = y) ∨ ((net.ends e).2 = x ∧ (net.ends e).1 = y)) →
      x ∈ V₀ := by
    intro x y hx hy he
    by_contra hxV
    have h0 : net.grad (fun z => 1 - g z) x = 0 := by
      rw [net.grad_const_sub g 1 x, hharm x hxV, neg_zero]
    have hneg : net.grad (fun z => 1 - g z) x < 0 := by
      refine net.grad_lt_zero_of_zero_at (fun z => 1 - g z) x (fun z => by linarith [hub z])
        (by simp [hx]) e ?_
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, by simp only [h2]; linarith⟩
      · exact Or.inr ⟨h1, by simp only [h2]; linarith⟩
    rw [h0] at hneg
    exact lt_irrefl 0 hneg
  have hb1 := hnn (net.ends e).1
  have hb2 := hnn (net.ends e).2
  have hu1 := hub (net.ends e).1
  have hu2 := hub (net.ends e).2
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).1 hosc with hd | hd
  · -- `g p = 1`, `g q = 0`
    have hp : g (net.ends e).1 = 1 := by linarith
    have hq : g (net.ends e).2 = 0 := by linarith
    exact ⟨hone _ (net.ends e).2 hp (by rw [hq]; norm_num) (Or.inl ⟨rfl, rfl⟩),
      hzero _ (net.ends e).1 hq (by rw [hp]; norm_num) (Or.inr ⟨rfl, rfl⟩)⟩
  · -- `g p = 0`, `g q = 1`
    have hp : g (net.ends e).1 = 0 := by linarith
    have hq : g (net.ends e).2 = 1 := by linarith
    exact ⟨hzero _ (net.ends e).2 hp (by rw [hq]; norm_num) (Or.inl ⟨rfl, rfl⟩),
      hone _ (net.ends e).1 hq (by rw [hp]; norm_num) (Or.inr ⟨rfl, rfl⟩)⟩

/--
**Lemma `sec31_continuous_harmonics`, the geometric input, proved.**

Let `net` be a finite network with two distinguished vertices `a ≠ b` (the
planting vertices), let `g` minimise the energy among the functions with
`g a = 0`, `g b = 1`, and assume

* the discrete Poincaré inequality `hP` (supplied by canonicality, see
  `poincare_of_path`), which makes the minimiser unique;
* **no shortcut edge**: no edge of the network joins `a` to `b` directly.  For an
  EIGS satisfying Assumption `ass:standing` this is automatic, see
  `IGS.Sec31.no_shortcut_of_distance_positive` and
  `IGS.Sec31.no_shortcut_of_two_le_dist`.

Then every edge oscillation of the `0`–`1` harmonic profile is *strictly* smaller
than `1`.
-/
theorem edge_osc_lt_one_of_no_shortcut (a b : V) (K : ℝ) (h : V → ℝ)
    (hP : ∀ g : V → ℝ, (∀ x ∈ ({a, b} : Finset V), g x = 0) → ∀ x, (g x) ^ 2 ≤ K * net.energy g)
    (ha : h a = 0) (hb : h b = 1) (g : V → ℝ)
    (hbd : ∀ x ∈ ({a, b} : Finset V), g x = h x)
    (hmin : ∀ f, (∀ x ∈ ({a, b} : Finset V), f x = h x) → net.energy g ≤ net.energy f)
    (hns : ∀ e : net.Edge,
      ¬ (((net.ends e).1 = a ∧ (net.ends e).2 = b) ∨ ((net.ends e).1 = b ∧ (net.ends e).2 = a))) :
    ∀ e : net.Edge, |g (net.ends e).1 - g (net.ends e).2| < 1 := by
  have hh : ∀ x ∈ ({a, b} : Finset V), 0 ≤ h x ∧ h x ≤ 1 := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [ha]; norm_num
    · rw [Finset.mem_singleton.1 hx, hb]; norm_num
  have hrange := net.range_subset_of_min ({a, b} : Finset V) h K hP hh g hbd hmin
  have hharm : ∀ x, x ∉ ({a, b} : Finset V) → net.grad g x = 0 := fun x hx =>
    net.grad_eq_zero_of_min ({a, b} : Finset V) h g hmin hbd x hx
  intro e
  have hb1 := (hrange (net.ends e).1)
  have hb2 := (hrange (net.ends e).2)
  have hle : |g (net.ends e).1 - g (net.ends e).2| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨h1, h2⟩ := net.mem_of_osc_one ({a, b} : Finset V) g hharm
      (fun y => (hrange y).1) (fun y => (hrange y).2) e heq
    -- the two endpoints are distinct and both lie in `{a,b}`, so the edge is a shortcut
    have hne : g (net.ends e).1 ≠ g (net.ends e).2 := by
      intro hcon; rw [hcon] at heq; simp at heq
    have hab : a ≠ b := by
      intro hcon; rw [hcon, hb] at ha; norm_num at ha
    rcases Finset.mem_insert.1 h1 with hp | hp <;> rcases Finset.mem_insert.1 h2 with hq | hq
    · exact hne (by rw [hp, hq])
    · exact hns e (Or.inl ⟨hp, Finset.mem_singleton.1 hq⟩)
    · exact hns e (Or.inr ⟨Finset.mem_singleton.1 hp, hq⟩)
    · exact hne (by rw [Finset.mem_singleton.1 hp, Finset.mem_singleton.1 hq])

omit [DecidableEq V] in
/-- The energy is a quadratic form: `ℰ(c + λ g) = λ² ℰ(g)`. -/
theorem energy_affine (g : V → ℝ) (c lam : ℝ) :
    net.energy (fun y => c + lam * g y) = lam ^ 2 * net.energy g := by
  unfold energy
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by ring

omit [DecidableEq V] in
/--
**Affine dependence on the boundary data.**  If `g` minimises the energy for the
boundary data `h`, then `c + λ g` minimises it for `c + λ h`.
-/
theorem min_affine (V₀ : Finset V) (h g : V → ℝ) (c lam : ℝ)
    (hmin : ∀ f, (∀ x ∈ V₀, f x = h x) → net.energy g ≤ net.energy f) :
    ∀ f, (∀ x ∈ V₀, f x = c + lam * h x) →
      net.energy (fun y => c + lam * g y) ≤ net.energy f := by
  intro f hf
  rcases eq_or_ne lam 0 with rfl | hlam
  · have hz : net.energy (fun y => c + (0:ℝ) * g y) = 0 := by
      rw [net.energy_affine g c 0]; ring
    rw [hz]
    exact net.energy_nonneg f
  · have hadm : ∀ x ∈ V₀, (fun y => (f y - c) / lam) x = h x := by
      intro x hx
      simp only
      rw [hf x hx]
      field_simp
      ring
    have h1 := hmin _ hadm
    have h2 : net.energy f = lam ^ 2 * net.energy (fun y => (f y - c) / lam) := by
      rw [← net.energy_affine (fun y => (f y - c) / lam) c lam]
      congr 1
      funext y
      field_simp
      ring
    rw [net.energy_affine g c lam, h2]
    have : (0:ℝ) < lam ^ 2 := by positivity
    nlinarith

omit [DecidableEq V] in
/--
**The contraction step.**  Let `g₀` be the `0`–`1` profile, with all its edge
oscillations bounded by `θ`.  Then the minimiser `g` for arbitrary boundary data
`p` at `a` and `q` at `b` — which equals `p + (q-p) g₀` by uniqueness — has all
its edge oscillations bounded by `θ · |q - p|`, i.e. by `θ` times the
oscillation of its own boundary data.

This is exactly the inequality "child-cell oscillation `≤ θ ·` parent-cell
oscillation" feeding the geometric decay `osc_n ≤ θ^n osc_0` of
`IGS.Sec31.osc_le_geometric`.
-/
theorem edge_osc_le_mul_of_profile (V₀ : Finset V) (K θ : ℝ) (h₀ : V → ℝ) (g₀ : V → ℝ)
    (hP : ∀ g : V → ℝ, (∀ x ∈ V₀, g x = 0) → ∀ x, (g x) ^ 2 ≤ K * net.energy g)
    (hbd₀ : ∀ x ∈ V₀, g₀ x = h₀ x)
    (hmin₀ : ∀ f, (∀ x ∈ V₀, f x = h₀ x) → net.energy g₀ ≤ net.energy f)
    (hθ : ∀ e : net.Edge, |g₀ (net.ends e).1 - g₀ (net.ends e).2| ≤ θ)
    (c lam : ℝ) (g : V → ℝ) (hbd : ∀ x ∈ V₀, g x = c + lam * h₀ x)
    (hmin : ∀ f, (∀ x ∈ V₀, f x = c + lam * h₀ x) → net.energy g ≤ net.energy f) :
    ∀ e : net.Edge, |g (net.ends e).1 - g (net.ends e).2| ≤ |lam| * θ := by
  have hbd' : ∀ x ∈ V₀, (fun y => c + lam * g₀ y) x = c + lam * h₀ x := by
    intro x hx; simp [hbd₀ x hx]
  have hmin' := net.min_affine V₀ h₀ g₀ c lam hmin₀
  have heq : g = fun y => c + lam * g₀ y :=
    net.min_unique V₀ (fun y => c + lam * h₀ y) K hP g _ hbd hbd' hmin hmin'
  intro e
  rw [heq]
  simp only
  have : c + lam * g₀ (net.ends e).1 - (c + lam * g₀ (net.ends e).2)
      = lam * (g₀ (net.ends e).1 - g₀ (net.ends e).2) := by ring
  rw [this, abs_mul]
  exact mul_le_mul_of_nonneg_left (hθ e) (abs_nonneg lam)

end FiniteNetwork

end IGS.Sec31
