import RequestProject.Section31.EIGSNativeResolventUniformSubsequence

/-! Compactness remains available after any strictly increasing selection of
levels. This is needed to identify every subsequential resolvent limit and
then prove convergence of the full sequence. -/

open Filter Topology
noncomputable section

namespace IGS.Sec31

theorem tendsto_of_every_strict_subsequence_has_further_limit
    {Space : Type*} [TopologicalSpace Space] (sequence : ℕ → Space) (limit : Space)
    (subsequenceLimit : ∀ levels : ℕ → ℕ, StrictMono levels →
      ∃ selection : ℕ → ℕ,
        Tendsto (fun index => sequence (levels (selection index))) atTop (𝓝 limit)) :
    Tendsto sequence atTop (𝓝 limit) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro levels levelsTendsto
  obtain ⟨increasing, _, composedStrict⟩ := strictMono_subseq_of_tendsto_atTop levelsTendsto
  obtain ⟨selection, convergence⟩ := subsequenceLimit (levels ∘ increasing) composedStrict
  exact ⟨increasing ∘ selection, convergence⟩

theorem uniform_subsequence_of_reindexed_finite_basis_approximations
    {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    {LevelVertex : ℕ → Type*} [∀ level, Fintype (LevelVertex level)]
    (embeddings : (level : ℕ) → LevelVertex level → Space)
    (nested : ∀ coarse fine, coarse ≤ fine → ∀ vertex : LevelVertex coarse,
      ∃ later : LevelVertex fine, embeddings fine later = embeddings coarse vertex)
    (dense : DenseRange (fun point : (level : ℕ) × LevelVertex level =>
      embeddings point.1 point.2))
    (values : (level : ℕ) → LevelVertex level → ℝ)
    {Coordinates : ℕ → Type*} [∀ depth, Fintype (Coordinates depth)]
    (basis : (depth : ℕ) → Coordinates depth → C(Space, ℝ))
    (coordinates : (depth : ℕ) → ℕ → Coordinates depth → ℝ)
    (bounded : ∀ depth, ∃ bound : ℝ, ∀ level, ‖coordinates depth level‖ ≤ bound)
    (errors : ℕ → ℝ) (errorsNonnegative : ∀ depth, 0 ≤ errors depth)
    (errorsConverge : Tendsto errors atTop (𝓝 0))
    (approximation : ∀ depth, ∀ᶠ level in atTop, ∀ vertex : LevelVertex level,
      |values level vertex - finiteBasisCombination (basis depth) (coordinates depth level)
        (embeddings level vertex)| ≤ errors depth)
    (levels : ℕ → ℕ) (levelsStrict : StrictMono levels) :
    ∃ selection : ℕ → ℕ, StrictMono selection ∧ ∃ limit : C(Space, ℝ),
      Tendsto (fun index => ‖fun vertex : LevelVertex (levels (selection index)) =>
        values (levels (selection index)) vertex -
          limit (embeddings (levels (selection index)) vertex)‖) atTop (𝓝 0) := by
  have selectedDense : DenseRange
      (fun point : (level : ℕ) × LevelVertex (levels level) =>
        embeddings (levels point.1) point.2) := by
    apply Dense.mono ?_ dense
    rintro point ⟨⟨level, vertex⟩, rfl⟩
    obtain ⟨later, equality⟩ := nested level (levels level) (levelsStrict.id_le level) vertex
    exact ⟨⟨level, later⟩, equality⟩
  apply uniform_subsequence_of_finite_basis_approximations
    (fun level => embeddings (levels level)) ?_ selectedDense
    (fun level => values (levels level)) basis
    (fun depth level => coordinates depth (levels level)) ?_
    errors errorsNonnegative errorsConverge ?_
  · intro coarse fine ordered vertex
    exact nested (levels coarse) (levels fine) (levelsStrict.monotone ordered) vertex
  · intro depth
    obtain ⟨bound, boundAll⟩ := bounded depth
    exact ⟨bound, fun level => boundAll (levels level)⟩
  · intro depth
    exact levelsStrict.tendsto_atTop.eventually (approximation depth)

end IGS.Sec31

#print axioms IGS.Sec31.uniform_subsequence_of_reindexed_finite_basis_approximations
#print axioms IGS.Sec31.tendsto_of_every_strict_subsequence_has_further_limit
