import RequestProject.Section31.Oscillation

/-!
# §3.1: the Markov property of the limit form

Reference: arXiv:2603.13798, §3.1, Theorem `thm:sec31_limit_dirichlet_form`
("the Markov property is inherited from the finite traces").

The Markov (Dirichlet) property of a form is the statement that composing with a
*normal contraction* — a `1`-Lipschitz map fixing `0` and mapping `[0,1]` into
itself, the clamp `t ↦ 0 ∨ (t ∧ 1)` being the canonical example — does not
increase the energy.  On a finite network this is an edgewise computation, and
it is proved here in the general Lipschitz form:

* `energy_comp_le_of_lipschitz` — `ℰ(T ∘ g) ≤ ℰ(g)` for every `1`-Lipschitz `T`;
* `energy_clamp_le` (in `Oscillation.lean`) — the special case of the clamp,
  which is also what powers the maximum principle there;
* `markov_of_iSup` — the property passes to the limit form
  `ℰ(u) = ⨆_m ℰ_m(u|_{V_m})` (Theorem `thm:sec31_limit_dirichlet_form` obtains
  the limit form as such a supremum of its finite traces, cf.
  `RequestProject/Section3/ResistanceForm.lean`).
-/

namespace IGS.Sec31

namespace FiniteNetwork

variable {V : Type*} (net : FiniteNetwork V)

/--
**The Markov property on a finite network.**
If `T : ℝ → ℝ` is `1`-Lipschitz then `ℰ(T ∘ g) ≤ ℰ(g)`.
-/
theorem energy_comp_le_of_lipschitz (T : ℝ → ℝ)
    (hT : ∀ s t : ℝ, |T s - T t| ≤ |s - t|) (g : V → ℝ) :
    net.energy (fun x => T (g x)) ≤ net.energy g := by
  refine Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left ?_ (net.cond_pos e).le
  have h := hT (g (net.ends e).1) (g (net.ends e).2)
  have h1 : |T (g (net.ends e).1) - T (g (net.ends e).2)| ^ 2
      ≤ |g (net.ends e).1 - g (net.ends e).2| ^ 2 := by
    nlinarith [abs_nonneg (T (g (net.ends e).1) - T (g (net.ends e).2)),
      abs_nonneg (g (net.ends e).1 - g (net.ends e).2)]
  simpa [sq_abs] using h1

end FiniteNetwork

/--
**The Markov property passes to a supremum of forms.**
If every finite trace `ℰ m` is Markovian for the contraction `T` and the limit
form is their supremum, then the limit form is Markovian too.
-/
theorem markov_of_iSup {A : Type*} (E : ℕ → A → ℝ) (Elim : A → ℝ)
    (hsup : ∀ u, Elim u = ⨆ m, E m u)
    (hbdd : ∀ u, BddAbove (Set.range fun m => E m u))
    (T : A → A) (hT : ∀ m u, E m (T u) ≤ E m u) (u : A) :
    Elim (T u) ≤ Elim u := by
  rw [hsup, hsup]
  exact ciSup_mono (hbdd u) fun m => hT m u

end IGS.Sec31
