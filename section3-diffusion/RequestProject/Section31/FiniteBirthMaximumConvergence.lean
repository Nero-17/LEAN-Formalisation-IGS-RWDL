import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! Finite early birth sets and a uniform tail imply convergence of the
actual finite-generation maxima. The limiting maximum is constructed and
attained internally; its existence is not an input. Candidate source. -/

namespace EIGS
open Filter Topology
noncomputable section

theorem finite_birth_maximum_convergence {Vertex : Type*} [Nonempty Vertex]
    (birth : Vertex → ℕ) (values : ℕ → Vertex → ℝ) (limits : Vertex → ℝ)
    (earlyFinite : ∀ threshold, {vertex | birth vertex < threshold}.Finite)
    (limitsPositive : ∀ vertex, 0 < limits vertex)
    (pointwise : ∀ vertex, Tendsto (fun level => values level vertex) atTop (𝓝 (limits vertex)))
    (uniformTail : ∀ epsilon : ℝ, 0 < epsilon → ∃ threshold : ℕ,
      ∀ level vertex, threshold ≤ birth vertex → values level vertex < epsilon)
    (maxima : ℕ → ℝ)
    (domination : ∀ level vertex, values level vertex ≤ maxima level)
    (attainment : ∀ level, ∃ vertex, maxima level = values level vertex) :
    ∃ maximizer : Vertex, 0 < limits maximizer ∧
      (∀ vertex, limits vertex ≤ limits maximizer) ∧
      Tendsto maxima atTop (𝓝 (limits maximizer)) := by
  classical
  obtain ⟨anchor⟩ := ‹Nonempty Vertex›
  obtain ⟨threshold, smallTail⟩ := uniformTail (limits anchor / 2)
    (half_pos (limitsPositive anchor))
  have tailLimit : ∀ vertex, threshold ≤ birth vertex → limits vertex ≤ limits anchor / 2 := by
    intro vertex late
    exact le_of_tendsto' (pointwise vertex) (fun level => (smallTail level vertex late).le)
  have anchorEarly : birth anchor < threshold := by
    by_contra late
    have comparison := tailLimit anchor (Nat.le_of_not_gt late)
    linarith [limitsPositive anchor]
  let earlyVertices := (earlyFinite threshold).toFinset
  have anchorMember : anchor ∈ earlyVertices := by
    simpa only [earlyVertices, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using anchorEarly
  have earlyNonempty : earlyVertices.Nonempty := ⟨anchor, anchorMember⟩
  obtain ⟨maximizer, maximizerMember, maximumValue⟩ :=
    Finset.exists_mem_eq_sup' earlyNonempty limits
  have earlyComparison : ∀ vertex ∈ earlyVertices, limits vertex ≤ limits maximizer := by
    intro vertex member
    exact (Finset.le_sup' limits member).trans_eq maximumValue
  have anchorComparison := earlyComparison anchor anchorMember
  have maximumPositive : 0 < limits maximizer := (limitsPositive anchor).trans_le anchorComparison
  have globalComparison : ∀ vertex, limits vertex ≤ limits maximizer := by
    intro vertex
    by_cases early : birth vertex < threshold
    · apply earlyComparison vertex
      simpa only [earlyVertices, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using early
    · exact (tailLimit vertex (Nat.le_of_not_gt early)).trans
        ((half_le_self (limitsPositive anchor).le).trans anchorComparison)
  refine ⟨maximizer, maximumPositive, globalComparison, tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro lower lowerStrict
    filter_upwards [(tendsto_order.mp (pointwise maximizer)).1 lower lowerStrict] with level above
    exact above.trans_le (domination level maximizer)
  · intro upper upperStrict
    have upperPositive : 0 < upper := maximumPositive.trans upperStrict
    obtain ⟨cutoff, tailBelow⟩ := uniformTail (upper / 2) (half_pos upperPositive)
    have earlyBelow : ∀ᶠ level in atTop,
        ∀ vertex ∈ {vertex | birth vertex < cutoff}, values level vertex < upper := by
      apply (earlyFinite cutoff).eventually_all.2
      intro vertex _
      exact (pointwise vertex).eventually_lt_const ((globalComparison vertex).trans_lt upperStrict)
    filter_upwards [earlyBelow] with level allEarly
    obtain ⟨vertex, equality⟩ := attainment level
    rw [equality]
    by_cases early : birth vertex < cutoff
    · exact allEarly vertex early
    · exact (tailBelow level vertex (Nat.le_of_not_gt early)).trans (half_lt_self upperPositive)

end
end EIGS

#print axioms EIGS.finite_birth_maximum_convergence
