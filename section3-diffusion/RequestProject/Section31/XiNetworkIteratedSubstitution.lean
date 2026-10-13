import RequestProject.Section2Concrete

namespace EIGS
variable {K : ℕ}

/-- The actual graph sequence and the generic network iteration agree as
whole networks, including their finite carriers and oriented edge maps. -/
theorem xiNetwork_add_substIter (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) :
    XiNetwork system (coarse + steps) =
      (XiNetwork system coarse).substIter (system.ruleFamily rulesConnected) steps := by
  induction steps with
  | zero => simp only [Nat.add_zero, Network.substIter_zero]
  | succ steps induction =>
      rw [Nat.add_succ, xiNetwork_succ system rulesConnected,
        Network.substIter_succ, induction]

theorem xiNetwork_eq_singleEdge_substIter (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (steps : ℕ) :
    XiNetwork system steps =
      (Network.singleEdge system.initCol).substIter (system.ruleFamily rulesConnected) steps := by
  simpa only [Nat.zero_add, xiNetwork_zero] using
    xiNetwork_add_substIter system rulesConnected 0 steps

end EIGS

#print axioms EIGS.xiNetwork_add_substIter
#print axioms EIGS.xiNetwork_eq_singleEdge_substIter
