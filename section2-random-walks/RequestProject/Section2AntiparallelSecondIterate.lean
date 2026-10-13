import RequestProject.Section2AntiparallelAudit
import RequestProject.Section2Concrete
import RequestProject.Section2Green

/-! A concrete second-iterate audit of the distinction between substituting
all directed arcs and taking the underlying undirected simple graph.
The resistance below is that of the actual Xi vertex quotient. -/

namespace EIGS.AntiparallelAudit

open scoped BigOperators Classical
open Matrix

set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

def system : EIGSData 1 where
  initCol := 0
  rule := fun _ =>
    { V := Vertex
      E := Fin 4
      tail := network.tail
      head := network.head
      col := fun _ => 0 }
  plantPlus := fun _ => Vertex.source
  plantMinus := fun _ => Vertex.sink
  plant_ne := fun _ => source_ne_sink

theorem rules_connected : ∀ colour, (ruleSG system colour).Connected := by
  intro colour
  letI : Nonempty (system.rule colour).V := ⟨Vertex.source⟩
  have reachesMiddle : ∀ vertex : Vertex, (ruleSG system colour).Reachable vertex Vertex.middle := by
    intro vertex
    cases vertex with
    | source =>
      apply SimpleGraph.Adj.reachable
      exact ⟨source_ne_middle, Or.inl ⟨(0 : Fin 4), rfl, rfl⟩⟩
    | middle => exact SimpleGraph.Reachable.refl _
    | sink =>
      apply SimpleGraph.Adj.reachable
      exact ⟨sink_ne_middle, Or.inl ⟨(3 : Fin 4), rfl, rfl⟩⟩
  exact ⟨fun first second => (reachesMiddle first).trans (reachesMiddle second).symm⟩

theorem planting_nonadjacent : ∀ colour,
    ¬ (ruleSG system colour).Adj (system.plantPlus colour) (system.plantMinus colour) := by
  intro colour
  change ¬ (Vertex.source ≠ Vertex.sink ∧
    ((∃ edge : Fin 4, network.tail edge = Vertex.source ∧ network.head edge = Vertex.sink) ∨
      ∃ edge : Fin 4, network.tail edge = Vertex.sink ∧ network.head edge = Vertex.source))
  dsimp only [network]
  norm_num [Fin.exists_fin_succ]

def secondSource : XiVtx system 2 := Sum.inl (Sum.inl false)
def secondSink : XiVtx system 2 := Sum.inl (Sum.inl true)

def secondMiddle : XiVtx system 2 :=
  Sum.inl (Sum.inr ⟨(), ⟨Vertex.middle, middle_ne_source, middle_ne_sink⟩⟩)

def secondPrivate (edge : Fin 4) : XiVtx system 2 :=
  Sum.inr ⟨⟨(), edge⟩, ⟨Vertex.middle, middle_ne_source, middle_ne_sink⟩⟩

def secondVertex : Fin 7 → XiVtx system 2 :=
  ![secondSource, secondMiddle, secondSink,
    secondPrivate 0, secondPrivate 1, secondPrivate 2, secondPrivate 3]

def secondVertexIndex : XiVtx system 2 → Fin 7
  | Sum.inl (Sum.inl false) => 0
  | Sum.inl (Sum.inl true) => 2
  | Sum.inl (Sum.inr _) => 1
  | Sum.inr interior => ⟨3 + Fin.val (n := 4) interior.1.2, by
      have bound := Fin.isLt (n := 4) interior.1.2
      omega⟩

theorem secondVertexIndex_vertex (vertex : Fin 7) :
    secondVertexIndex (secondVertex vertex) = vertex := by
  fin_cases vertex <;> rfl

theorem secondVertex_bijective : Function.Bijective secondVertex := by
  constructor
  · intro first second equality
    have decoded := congrArg secondVertexIndex equality
    simpa only [secondVertexIndex_vertex] using decoded
  · intro vertex
    rcases vertex with old | ⟨⟨unit, edge⟩, ⟨interior, plus, minus⟩⟩
    · rcases old with terminal | ⟨unit, ⟨interior, plus, minus⟩⟩
      · cases terminal
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
      · cases unit
        cases interior with
        | source => exact False.elim (plus rfl)
        | middle => exact ⟨1, rfl⟩
        | sink => exact False.elim (minus rfl)
    · cases unit
      cases interior with
      | source => exact False.elim (plus rfl)
      | sink => exact False.elim (minus rfl)
      | middle =>
        fin_cases edge
        · exact ⟨3, rfl⟩
        · exact ⟨4, rfl⟩
        · exact ⟨5, rfl⟩
        · exact ⟨6, rfl⟩

theorem secondVertex_eq_iff (first second : Fin 7) :
    secondVertex first = secondVertex second ↔ first = second :=
  secondVertex_bijective.injective.eq_iff

def secondEdge (first second : Fin 4) : XiEdge system.toRuleData 2 :=
  ⟨⟨(), first⟩, second⟩

theorem exists_secondEdge (predicate : XiEdge system.toRuleData 2 → Prop) :
    (∃ edge, predicate edge) ↔ ∃ first second : Fin 4, predicate (secondEdge first second) := by
  constructor
  · rintro ⟨⟨⟨unit, first⟩, second⟩, property⟩
    cases unit
    exact ⟨first, second, property⟩
  · rintro ⟨first, second, property⟩
    exact ⟨secondEdge first second, property⟩

def secondTailIndex : Fin 4 → Fin 4 → Fin 7 :=
  ![![0, 3, 3, 1], ![1, 4, 4, 0], ![1, 5, 5, 2], ![2, 6, 6, 1]]

def secondHeadIndex : Fin 4 → Fin 4 → Fin 7 :=
  ![![3, 0, 1, 3], ![4, 1, 0, 4], ![5, 1, 2, 5], ![6, 2, 1, 6]]

theorem secondEdge_tail (first second : Fin 4) :
    XiTail system 2 (secondEdge first second) = secondVertex (secondTailIndex first second) := by
  fin_cases first <;> fin_cases second <;> rfl

theorem secondEdge_head (first second : Fin 4) :
    XiHead system 2 (secondEdge first second) = secondVertex (secondHeadIndex first second) := by
  fin_cases first <;> fin_cases second <;> rfl

def secondNeighbors : Fin 7 → Finset (Fin 7) :=
  ![{3, 4}, {3, 4, 5, 6}, {5, 6}, {0, 1}, {0, 1}, {1, 2}, {1, 2}]

theorem second_adjacency (first second : Fin 7) :
    (XiSimpleGraph system 2).Adj (secondVertex first) (secondVertex second) ↔
      second ∈ secondNeighbors first := by
  change (secondVertex first ≠ secondVertex second ∧
    ((∃ edge, XiTail system 2 edge = secondVertex first ∧
        XiHead system 2 edge = secondVertex second) ∨
      ∃ edge, XiTail system 2 edge = secondVertex second ∧
        XiHead system 2 edge = secondVertex first)) ↔ _
  rw [exists_secondEdge, exists_secondEdge]
  simp_rw [secondEdge_tail, secondEdge_head, secondVertex_eq_iff]
  revert first second
  decide

noncomputable def secondPotential : XiVtx system 2 → ℝ
  | Sum.inl (Sum.inl false) => 2
  | Sum.inl (Sum.inl true) => 0
  | Sum.inl (Sum.inr _) => 1
  | Sum.inr interior => if Fin.val (n := 4) interior.1.2 < (2 : ℕ) then 3 / 2 else 1 / 2

theorem secondPotential_vertex (vertex : Fin 7) :
    secondPotential (secondVertex vertex) = (![2, 1, 0, 3 / 2, 3 / 2, 1 / 2, 1 / 2] : Fin 7 → ℝ) vertex := by
  fin_cases vertex <;> norm_num [secondPotential, secondVertex, secondSource, secondMiddle,
    secondSink, secondPrivate]

/-- Reading the Dirichlet inverse from a genuinely verified unit-current
potential avoids assuming any resistance value. -/
theorem resistance_eq_of_unit_current_potential
    {Vertices : Type} [Fintype Vertices] [DecidableEq Vertices]
    (graph : SimpleGraph Vertices) [DecidableRel graph.Adj]
    (connected : graph.Connected) (source sink : Vertices) (distinct : source ≠ sink)
    (potential : Vertices → ℝ) (sinkZero : potential sink = 0)
    (laplacian : ∀ vertex, vertex ≠ sink →
      (graph.lapMatrix ℝ *ᵥ potential) vertex = if vertex = source then 1 else 0) :
    effResToBoundary graph (Finset.univ.erase sink) source = potential source := by
  have sourceInside : source ∈ Finset.univ.erase sink := by simp [distinct]
  have boundaryNonempty : (Finset.univ.erase sink)ᶜ.Nonempty := ⟨sink, by simp⟩
  have equalLaplacian :
      dirichletLap graph (Finset.univ.erase sink) *ᵥ
          (fun vertex : Finset.univ.erase sink => potential vertex) =
      dirichletLap graph (Finset.univ.erase sink) *ᵥ
          (fun vertex : Finset.univ.erase sink =>
            unitPotential graph (Finset.univ.erase sink) source vertex) := by
    funext vertex
    rw [← lapMatrix_mulVec_restrict graph _ potential
      (by
        intro outside notInside
        have equality : outside = sink := by simpa using notInside
        simpa only [equality] using sinkZero)
      vertex vertex.property]
    rw [← lapMatrix_mulVec_restrict graph _ (unitPotential graph (Finset.univ.erase sink) source)
      (by intro outside notInside; simp [unitPotential, notInside]) vertex vertex.property]
    rw [laplacian vertex (Finset.mem_erase.mp vertex.property).1,
      lapMatrix_mulVec_unitPotential graph connected boundaryNonempty sourceInside vertex vertex.property]
  have equalPotential := congrArg ((greenFn graph (Finset.univ.erase sink)).mulVec) equalLaplacian
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    mul_eq_one_comm.mp (dirichletLap_mul_greenFn graph connected boundaryNonempty),
    Matrix.one_mulVec, Matrix.one_mulVec] at equalPotential
  have sourceEquality := congrFun equalPotential ⟨source, sourceInside⟩
  rw [green_diag_eq_resistance graph connected boundaryNonempty sourceInside]
  simpa only [unitPotential_apply_mem graph sourceInside sourceInside] using sourceEquality.symm

theorem second_potential_laplacian : ∀ vertex : XiVtx system 2,
    ((XiSimpleGraph system 2).lapMatrix ℝ *ᵥ secondPotential) vertex =
      if vertex = secondSource then 1 else if vertex = secondSink then -1 else 0 := by
  intro actualVertex
  obtain ⟨vertex, rfl⟩ := secondVertex_bijective.surjective actualVertex
  change _ = if secondVertex vertex = secondVertex 0 then 1
    else if secondVertex vertex = secondVertex 2 then -1 else 0
  simp only [secondVertex_eq_iff]
  rw [SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.degree_eq_sum_if_adj]
  rw [← secondVertex_bijective.sum_comp
    (fun other => if (XiSimpleGraph system 2).Adj (secondVertex vertex) other then (1 : ℝ) else 0)]
  rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  rw [← secondVertex_bijective.sum_comp
    (fun other => if (XiSimpleGraph system 2).Adj (secondVertex vertex) other
      then secondPotential other else 0)]
  simp only [second_adjacency, secondPotential_vertex]
  simp only [Fin.sum_univ_succ]
  fin_cases vertex <;> norm_num [secondNeighbors, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem actual_second_iterate_simple_resistance :
    effResToBoundary (XiSimpleGraph system 2) (Finset.univ.erase secondSink) secondSource = 2 := by
  have calculated := resistance_eq_of_unit_current_potential (XiSimpleGraph system 2)
    (xiSimpleGraph_connected system rules_connected 2) secondSource secondSink
    (by decide) secondPotential rfl (by
      intro vertex notSink
      simpa only [notSink, if_false] using second_potential_laplacian vertex)
  simpa only [secondPotential, secondSource] using calculated

/-- One chosen orientation of each edge of the actual underlying simple rule. -/
def simpleRule : Network 1 where
  V := Vertex
  E := Fin 2
  fintypeV := inferInstance
  decEqV := inferInstance
  fintypeE := inferInstance
  tail := ![Vertex.source, Vertex.middle]
  head := ![Vertex.middle, Vertex.sink]
  color := fun _ => 0

theorem simpleRule_graph_eq_original_underlying :
    simpleRule.toSimpleGraph = ruleSG system 0 := by
  ext first second
  dsimp only [Network.toSimpleGraph, ruleSG, SimpleGraph.fromRel, simpleRule, system, network]
  cases first <;> cases second <;>
    norm_num [Fin.exists_fin_succ]

noncomputable def simpleRuleFlow : simpleRule.Flow Vertex.source Vertex.sink :=
  ⟨![1, 1], by
    intro vertex
    dsimp only [Network.div, simpleRule]
    cases vertex <;> norm_num [Fin.sum_univ_succ]⟩

noncomputable def simpleRulePsi (resistance : ℝ) : ℝ :=
  simpleRule.effRes Vertex.source Vertex.sink ⟨simpleRuleFlow⟩ (fun _ => resistance)

theorem simpleRulePsi_eq (resistance : ℝ) : simpleRulePsi resistance = 2 * resistance := by
  letI : Nonempty (simpleRule.Flow Vertex.source Vertex.sink) := ⟨simpleRuleFlow⟩
  have energyConstant : ∀ current : simpleRule.Flow Vertex.source Vertex.sink,
      simpleRule.energyNetwork current.val (fun _ => resistance) = 2 * resistance := by
    intro current
    have sourceCurrent := current.property Vertex.source
    have sinkCurrent := current.property Vertex.sink
    dsimp only [Network.div, simpleRule] at sourceCurrent sinkCurrent
    norm_num [Fin.sum_univ_succ] at sourceCurrent sinkCurrent
    dsimp only [Network.energyNetwork, simpleRule]
    norm_num [Fin.sum_univ_succ, sourceCurrent, sinkCurrent] <;>
      linarith
  rw [simpleRulePsi, Network.effRes_eq_iInf]
  simp only [energyConstant, ciInf_const]

theorem actual_second_iterate_ne_simple_rule_iteration :
    effResToBoundary (XiSimpleGraph system 2) (Finset.univ.erase secondSink) secondSource ≠
      simpleRulePsi (simpleRulePsi 1) := by
  rw [actual_second_iterate_simple_resistance, simpleRulePsi_eq, simpleRulePsi_eq]
  norm_num

end EIGS.AntiparallelAudit

#print axioms EIGS.AntiparallelAudit.rules_connected
#print axioms EIGS.AntiparallelAudit.second_potential_laplacian
#print axioms EIGS.AntiparallelAudit.actual_second_iterate_simple_resistance
#print axioms EIGS.AntiparallelAudit.simpleRule_graph_eq_original_underlying
#print axioms EIGS.AntiparallelAudit.simpleRulePsi_eq
#print axioms EIGS.AntiparallelAudit.actual_second_iterate_ne_simple_rule_iteration
