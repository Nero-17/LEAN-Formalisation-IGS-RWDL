import RequestProject.Section31.UniformCadlagClosed

/-! Expose the existing genuine cadlag subtype pseudometric to instance
search. CadlagJ1Path is a definition, so its subtype structure is not unfolded
by typeclass synthesis automatically. The distance and topology are exactly
those inherited from J1Function; no new separation assertion is made. -/

namespace IGS.Sec31.DiscreteMarkov
noncomputable section

noncomputable instance cadlagJ1CarrierPseudoMetricSpace
    {Time State : Type*} [LinearOrder Time] [MetricSpace Time] [BoundedSpace Time]
    [MetricSpace State] [BoundedSpace State] : PseudoMetricSpace (CadlagJ1Path Time State) :=
  inferInstanceAs (PseudoMetricSpace {path : J1Function Time State // IsCadlagPath path.toFun})

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.cadlagJ1CarrierPseudoMetricSpace
