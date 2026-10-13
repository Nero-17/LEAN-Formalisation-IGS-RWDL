import RequestProject.Section2StarCounts
import RequestProject.Section2StarResistance

/-! The actual fine-graph boundary of an incident star consists of other
coarse vertices. This is an adjacency statement, independent of harmonic
trace laws or any stopping-time identification. -/

namespace EIGS

open scoped Classical
variable {K : ℕ}

theorem xiIncidentStar_embedRuleVtx_outside_of_incident (system : EIGSData K)
    (coarse steps : ℕ) (center : XiVtx system coarse)
    (edge : XiEdge system.toRuleData (coarse + steps))
    (incident : xiIncidentStar system coarse center steps (XiTail system (coarse + steps) edge) ∨
      xiIncidentStar system coarse center steps (XiHead system (coarse + steps) edge))
    (vertex : (system.rule (XiCol system.toRuleData (coarse + steps) edge)).V)
    (outside : ¬ xiIncidentStar system coarse center (steps + 1)
      (embedRuleVtx system (coarse + steps) edge (XiTail system (coarse + steps) edge)
        (XiHead system (coarse + steps) edge) vertex)) :
    (vertex = system.plantPlus (XiCol system.toRuleData (coarse + steps) edge) ∧
      ¬ xiIncidentStar system coarse center steps (XiTail system (coarse + steps) edge)) ∨
    (vertex = system.plantMinus (XiCol system.toRuleData (coarse + steps) edge) ∧
      ¬ xiIncidentStar system coarse center steps (XiHead system (coarse + steps) edge)) := by
  by_cases plus : vertex = system.plantPlus (XiCol system.toRuleData (coarse + steps) edge)
  · subst vertex
    rw [embedRuleVtx_plantPlus] at outside
    exact Or.inl ⟨rfl, outside⟩
  · by_cases minus : vertex = system.plantMinus (XiCol system.toRuleData (coarse + steps) edge)
    · subst vertex
      rw [embedRuleVtx_plantMinus] at outside
      exact Or.inr ⟨rfl, outside⟩
    · exact (outside (by
        simpa only [embedRuleVtx, plus, minus, ↓reduceDIte, xiIncidentStar] using incident)).elim

/-- If an actual fine edge touches the star, each endpoint outside the star
is an original coarse vertex distinct from the star center. -/
theorem xiIncidentStar_outside_endpoint (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) (edge : XiEdge system.toRuleData (coarse + steps))
    (incident : xiIncidentStar system coarse center steps (XiTail system (coarse + steps) edge) ∨
      xiIncidentStar system coarse center steps (XiHead system (coarse + steps) edge))
    (vertex : XiVtx system (coarse + steps))
    (endpoint : vertex = XiTail system (coarse + steps) edge ∨
      vertex = XiHead system (coarse + steps) edge)
    (outside : ¬ xiIncidentStar system coarse center steps vertex) :
    ∃ other : XiVtx system coarse, other ≠ center ∧ vertex = xiForward system coarse steps other := by
  induction steps with
  | zero => exact ⟨vertex, outside, rfl⟩
  | succ steps induction_hypothesis =>
      rcases edge with ⟨parent, child⟩
      have parent_incident :
          xiIncidentStar system coarse center steps (XiTail system (coarse + steps) parent) ∨
          xiIncidentStar system coarse center steps (XiHead system (coarse + steps) parent) := by
        rcases incident with incident | incident
        · exact xiIncidentStar_embedRuleVtx_imp system coarse steps center parent _ incident
        · exact xiIncidentStar_embedRuleVtx_imp system coarse steps center parent _ incident
      have embedded_outside (rule_vertex : (system.rule (XiCol system.toRuleData (coarse + steps) parent)).V)
          (not_inside : ¬ xiIncidentStar system coarse center (steps + 1)
            (embedRuleVtx system (coarse + steps) parent (XiTail system (coarse + steps) parent)
              (XiHead system (coarse + steps) parent) rule_vertex)) :
          ∃ other : XiVtx system coarse, other ≠ center ∧
            embedRuleVtx system (coarse + steps) parent (XiTail system (coarse + steps) parent)
              (XiHead system (coarse + steps) parent) rule_vertex =
                xiForward system coarse (steps + 1) other := by
        rcases xiIncidentStar_embedRuleVtx_outside_of_incident system coarse steps center parent
            parent_incident rule_vertex not_inside with ⟨equal, not_tail⟩ | ⟨equal, not_head⟩
        · rw [equal, embedRuleVtx_plantPlus]
          obtain ⟨other, different, same⟩ := induction_hypothesis parent parent_incident
            (XiTail system (coarse + steps) parent) (Or.inl rfl) not_tail
          exact ⟨other, different, congrArg Sum.inl same⟩
        · rw [equal, embedRuleVtx_plantMinus]
          obtain ⟨other, different, same⟩ := induction_hypothesis parent parent_incident
            (XiHead system (coarse + steps) parent) (Or.inr rfl) not_head
          exact ⟨other, different, congrArg Sum.inl same⟩
      rcases endpoint with rfl | rfl
      · exact embedded_outside ((system.rule _).tail child) outside
      · exact embedded_outside ((system.rule _).head child) outside

theorem xiIncidentStarDomain_forward_mem_iff (system : EIGSData K) (coarse steps : ℕ)
    (center other : XiVtx system coarse) :
    xiForward system coarse steps other ∈ xiIncidentStarDomain system coarse steps center ↔
      other = center := by
  simp only [xiIncidentStarDomain, Finset.mem_filter, Finset.mem_univ, true_and,
    xiIncidentStar_forward_iff]

/-- A genuine adjacent step leaving the star lands on a distinct coarse
vertex. This supplies the deterministic boundary fact for regeneration. -/
theorem xiIncidentStarDomain_adj_outside (system : EIGSData K) (coarse steps : ℕ)
    (center : XiVtx system coarse) {inside outside : XiVtx system (coarse + steps)}
    (inside_mem : inside ∈ xiIncidentStarDomain system coarse steps center)
    (outside_not_mem : outside ∉ xiIncidentStarDomain system coarse steps center)
    (adjacency : (XiSimpleGraph system (coarse + steps)).Adj inside outside) :
    ∃ other : XiVtx system coarse, other ≠ center ∧ outside = xiForward system coarse steps other := by
  have inside_star : xiIncidentStar system coarse center steps inside :=
    (Finset.mem_filter.mp inside_mem).2
  have outside_star : ¬ xiIncidentStar system coarse center steps outside := by
    intro membership
    exact outside_not_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, membership⟩)
  rcases adjacency.2 with ⟨edge, tail, head⟩ | ⟨edge, tail, head⟩
  · exact xiIncidentStar_outside_endpoint system coarse steps center edge
      (Or.inl (by simpa only [tail] using inside_star)) outside (Or.inr head.symm) outside_star
  · exact xiIncidentStar_outside_endpoint system coarse steps center edge
      (Or.inr (by simpa only [head] using inside_star)) outside (Or.inl tail.symm) outside_star

end EIGS

#print axioms EIGS.xiIncidentStar_embedRuleVtx_outside_of_incident
#print axioms EIGS.xiIncidentStar_outside_endpoint
#print axioms EIGS.xiIncidentStarDomain_forward_mem_iff
#print axioms EIGS.xiIncidentStarDomain_adj_outside
