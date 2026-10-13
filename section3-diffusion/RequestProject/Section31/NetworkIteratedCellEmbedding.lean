import RequestProject.Section31.NetworkSubstitutionLocalization

/-!
Actual cell embeddings through repeated network substitution. Vertex and
edge injections are transported together, with exact endpoints and colours.
This construction does not assume local adjacency, killed-chain transport,
or any exit-time estimate. Interior localization is a subsequent obligation.
-/

namespace EIGS.RuleFamily

open scoped Classical

variable {K : ℕ} (rules : EIGS.RuleFamily K)

noncomputable def vertexColourEquiv {first second : Fin K} (equal : first = second) :
    (rules.R first).V ≃ (rules.R second).V := by subst second; exact Equiv.refl _

noncomputable def edgeColourEquiv {first second : Fin K} (equal : first = second) :
    (rules.R first).E ≃ (rules.R second).E := by subst second; exact Equiv.refl _

noncomputable def innerColourEquiv {first second : Fin K} (equal : first = second) :
    {vertex : (rules.R first).V // vertex ≠ rules.βplus first ∧ vertex ≠ rules.βminus first} ≃
    {vertex : (rules.R second).V // vertex ≠ rules.βplus second ∧ vertex ≠ rules.βminus second} := by
  subst second
  exact Equiv.refl _

@[simp] theorem vertexColourEquiv_plus {first second : Fin K} (equal : first = second) :
    rules.vertexColourEquiv equal (rules.βplus first) = rules.βplus second := by cases equal; rfl

@[simp] theorem vertexColourEquiv_minus {first second : Fin K} (equal : first = second) :
    rules.vertexColourEquiv equal (rules.βminus first) = rules.βminus second := by cases equal; rfl

@[simp] theorem innerColourEquiv_val {first second : Fin K} (equal : first = second)
    (vertex : {vertex : (rules.R first).V // vertex ≠ rules.βplus first ∧ vertex ≠ rules.βminus first}) :
    (rules.innerColourEquiv equal vertex).val = rules.vertexColourEquiv equal vertex.val := by
  cases equal
  rfl

theorem vertexColourEquiv_eq_plus {first second : Fin K} (equal : first = second)
    (vertex : (rules.R first).V) :
    rules.vertexColourEquiv equal vertex = rules.βplus second ↔ vertex = rules.βplus first := by
  rw [← rules.vertexColourEquiv_plus equal]
  exact (rules.vertexColourEquiv equal).injective.eq_iff

theorem vertexColourEquiv_eq_minus {first second : Fin K} (equal : first = second)
    (vertex : (rules.R first).V) :
    rules.vertexColourEquiv equal vertex = rules.βminus second ↔ vertex = rules.βminus first := by
  rw [← rules.vertexColourEquiv_minus equal]
  exact (rules.vertexColourEquiv equal).injective.eq_iff

theorem edgeColourEquiv_tail {first second : Fin K} (equal : first = second)
    (edge : (rules.R first).E) :
    rules.vertexColourEquiv equal ((rules.R first).tail edge) =
      (rules.R second).tail (rules.edgeColourEquiv equal edge) := by cases equal; rfl

theorem edgeColourEquiv_head {first second : Fin K} (equal : first = second)
    (edge : (rules.R first).E) :
    rules.vertexColourEquiv equal ((rules.R first).head edge) =
      (rules.R second).head (rules.edgeColourEquiv equal edge) := by cases equal; rfl

theorem edgeColourEquiv_colour {first second : Fin K} (equal : first = second)
    (edge : (rules.R first).E) :
    (rules.R first).color edge = (rules.R second).color (rules.edgeColourEquiv equal edge) := by
  cases equal
  rfl

end EIGS.RuleFamily

namespace EIGS.Network

open scoped Classical
noncomputable section

variable {K : ℕ}

/-- Literal injections of vertices and coloured oriented edges, preserving
the actual endpoint maps. No metric or probabilistic property is assumed. -/
structure ColourEmbedding (source target : EIGS.Network K) where
  vertex : source.V ↪ target.V
  edge : source.E ↪ target.E
  tail : ∀ original_edge, vertex (source.tail original_edge) = target.tail (edge original_edge)
  head : ∀ original_edge, vertex (source.head original_edge) = target.head (edge original_edge)
  colour : ∀ original_edge, source.color original_edge = target.color (edge original_edge)

namespace ColourEmbedding

variable {source target : EIGS.Network K} (embedding : ColourEmbedding source target)
    (rules : EIGS.RuleFamily K)

def substVertex : (source.subst rules).V ↪ (target.subst rules).V :=
  Function.Embedding.sumMap embedding.vertex
    (Function.Embedding.sigmaMap embedding.edge (fun edge =>
      (rules.innerColourEquiv (embedding.colour edge)).toEmbedding))

def substEdge : (source.subst rules).E ↪ (target.subst rules).E :=
  Function.Embedding.sigmaMap embedding.edge (fun edge =>
    (rules.edgeColourEquiv (embedding.colour edge)).toEmbedding)

@[simp] theorem substVertex_old (vertex : source.V) :
    embedding.substVertex rules (Sum.inl vertex) = Sum.inl (embedding.vertex vertex) := rfl

@[simp] theorem substVertex_private (edge : source.E) (vertex : source.SubstInner rules edge) :
    embedding.substVertex rules (Sum.inr ⟨edge, vertex⟩) =
      Sum.inr ⟨embedding.edge edge, rules.innerColourEquiv (embedding.colour edge) vertex⟩ := rfl

/-- The functorial vertex injection commutes with the actual terminal
gluing map, including private interior points. -/
theorem substVertex_embed (edge : source.E) (vertex : (rules.R (source.color edge)).V) :
    embedding.substVertex rules (source.substEmbed rules edge vertex) =
      target.substEmbed rules (embedding.edge edge)
        (rules.vertexColourEquiv (embedding.colour edge) vertex) := by
  by_cases plus : vertex = rules.βplus (source.color edge)
  · subst vertex
    simp only [Network.substEmbed, rules.vertexColourEquiv_plus, ↓reduceDIte,
      substVertex_old, embedding.tail]
  · by_cases minus : vertex = rules.βminus (source.color edge)
    · subst vertex
      simp only [Network.substEmbed, rules.vertexColourEquiv_minus,
        (rules.plant_ne (source.color edge)).symm,
        (rules.plant_ne (target.color (embedding.edge edge))).symm,
        ↓reduceDIte, substVertex_old, embedding.head]
    · have mapped_plus : rules.vertexColourEquiv (embedding.colour edge) vertex ≠
          rules.βplus (target.color (embedding.edge edge)) := by
        intro equal
        exact plus ((rules.vertexColourEquiv_eq_plus (embedding.colour edge) vertex).mp equal)
      have mapped_minus : rules.vertexColourEquiv (embedding.colour edge) vertex ≠
          rules.βminus (target.color (embedding.edge edge)) := by
        intro equal
        exact minus ((rules.vertexColourEquiv_eq_minus (embedding.colour edge) vertex).mp equal)
      simp only [Network.substEmbed, plus, minus, mapped_plus, mapped_minus, ↓reduceDIte]
      rw [substVertex_private]
      apply congrArg Sum.inr
      apply congrArg (Sigma.mk (embedding.edge edge))
      apply Subtype.ext
      exact rules.innerColourEquiv_val (embedding.colour edge) ⟨vertex, plus, minus⟩

/-- Actual substitution acts on the literal coloured network embeddings. -/
def subst : ColourEmbedding (source.subst rules) (target.subst rules) where
  vertex := embedding.substVertex rules
  edge := embedding.substEdge rules
  tail edge := by
    rcases edge with ⟨parent, child⟩
    change embedding.substVertex rules (source.substEmbed rules parent
        ((rules.R (source.color parent)).tail child)) =
      target.substEmbed rules (embedding.edge parent)
        ((rules.R (target.color (embedding.edge parent))).tail
          (rules.edgeColourEquiv (embedding.colour parent) child))
    rw [← rules.edgeColourEquiv_tail (embedding.colour parent) child]
    exact embedding.substVertex_embed rules parent _
  head edge := by
    rcases edge with ⟨parent, child⟩
    change embedding.substVertex rules (source.substEmbed rules parent
        ((rules.R (source.color parent)).head child)) =
      target.substEmbed rules (embedding.edge parent)
        ((rules.R (target.color (embedding.edge parent))).head
          (rules.edgeColourEquiv (embedding.colour parent) child))
    rw [← rules.edgeColourEquiv_head (embedding.colour parent) child]
    exact embedding.substVertex_embed rules parent _
  colour edge := by
    rcases edge with ⟨parent, child⟩
    exact rules.edgeColourEquiv_colour (embedding.colour parent) child

def substIter : (level : ℕ) → ColourEmbedding (source.substIter rules level) (target.substIter rules level) :=
  fun level => Nat.rec
    (motive := fun level => ColourEmbedding (source.substIter rules level) (target.substIter rules level))
    embedding (fun _ induction_hypothesis => induction_hypothesis.subst rules) level

theorem substIter_old (vertex : source.V) (level : ℕ) :
    (embedding.substIter rules level).vertex (source.inlIter rules vertex level) =
      target.inlIter rules (embedding.vertex vertex) level := by
  induction level with
  | zero => rfl
  | succ level induction_hypothesis =>
      change Sum.inl ((embedding.substIter rules level).vertex (source.inlIter rules vertex level)) =
        Sum.inl (target.inlIter rules (embedding.vertex vertex) level)
      rw [induction_hypothesis]

end ColourEmbedding

/-- The first actual private rule copy is a literal colour-preserving
network embedding. Its injectivity follows from distinct actual endpoints. -/
def firstCopyEmbedding (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (loopless : network.Loopless) (edge : network.E) :
    ColourEmbedding (rules.R (network.color edge)) (network.subst rules) where
  vertex := ⟨network.substEmbed rules edge, network.substEmbed_injective rules loopless edge⟩
  edge := Function.Embedding.sigmaMk
    (β := fun parent : network.E => (rules.R (network.color parent)).E) edge
  tail _ := rfl
  head _ := rfl
  colour _ := rfl

/-- A first-generation cell embedded after any further number of actual
substitutions, with endpoint/colour preservation inherited at every depth. -/
def iteratedCellEmbedding (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (loopless : network.Loopless) (edge : network.E) (level : ℕ) :
    ColourEmbedding ((rules.R (network.color edge)).substIter rules level)
      ((network.subst rules).substIter rules level) :=
  (network.firstCopyEmbedding rules loopless edge).substIter rules level

theorem iteratedCellEmbedding_plus (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (loopless : network.Loopless) (edge : network.E) (level : ℕ) :
    (network.iteratedCellEmbedding rules loopless edge level).vertex
        ((rules.R (network.color edge)).inlIter rules (rules.βplus (network.color edge)) level) =
      (network.subst rules).inlIter rules (Sum.inl (network.tail edge)) level := by
  change ((network.firstCopyEmbedding rules loopless edge).substIter rules level).vertex _ = _
  rw [ColourEmbedding.substIter_old]
  change (network.subst rules).inlIter rules
    (network.substEmbed rules edge (rules.βplus (network.color edge))) level = _
  simp only [Network.substEmbed, ↓reduceDIte]

theorem iteratedCellEmbedding_minus (network : EIGS.Network K) (rules : EIGS.RuleFamily K)
    (loopless : network.Loopless) (edge : network.E) (level : ℕ) :
    (network.iteratedCellEmbedding rules loopless edge level).vertex
        ((rules.R (network.color edge)).inlIter rules (rules.βminus (network.color edge)) level) =
      (network.subst rules).inlIter rules (Sum.inl (network.head edge)) level := by
  change ((network.firstCopyEmbedding rules loopless edge).substIter rules level).vertex _ = _
  rw [ColourEmbedding.substIter_old]
  change (network.subst rules).inlIter rules
    (network.substEmbed rules edge (rules.βminus (network.color edge))) level = _
  simp only [Network.substEmbed,
    (rules.plant_ne (network.color edge)).symm, ↓reduceDIte]

end
end EIGS.Network

#print axioms EIGS.Network.ColourEmbedding.substVertex_embed
#print axioms EIGS.Network.ColourEmbedding.substIter_old
#print axioms EIGS.Network.iteratedCellEmbedding
#print axioms EIGS.Network.iteratedCellEmbedding_plus
#print axioms EIGS.Network.iteratedCellEmbedding_minus
