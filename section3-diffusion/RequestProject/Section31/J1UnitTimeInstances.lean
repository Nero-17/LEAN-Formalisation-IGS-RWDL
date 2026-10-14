import RequestProject.Section31.J1IntervalOneKnotAlignment

namespace IGS.Sec31.DiscreteMarkov
noncomputable section

instance unitJ1TimeBoundedSpace : BoundedSpace UnitJ1Time :=
  ⟨Metric.isBounded_of_compactSpace⟩

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.unitJ1TimeBoundedSpace
