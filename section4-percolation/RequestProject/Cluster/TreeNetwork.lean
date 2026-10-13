import RequestProject.Cluster.Coupling

/-!
# Actual unit-resistance networks encoded by replacement trees

Each tree recursively constructs a genuine two-terminal electrical network.
Its effective resistance is the resistance variable used in the probability
recursion. A concrete embedding as an open subnetwork of the DHL supplies
the bridge to the already proved percolation-network resistance identities.
-/

namespace Cluster

open Reduced

noncomputable section

/-- The completely closed configuration at a fixed DHL depth. -/
def closedConfiguration : (n : ℕ) → Conf n
  | 0 => false
  | n + 1 =>
      (closedConfiguration n, closedConfiguration n, closedConfiguration n, closedConfiguration n)

@[simp] theorem closedConfiguration_connection (n : ℕ) :
    conn n (closedConfiguration n) = false := by
  induction n with
  | zero => rfl
  | succ n induction_hypothesis => simp [closedConfiguration, conn_succ, induction_hypothesis]

@[simp] theorem closedConfiguration_resistance (n : ℕ) :
    res n (closedConfiguration n) = ⊤ := by
  by_contra finite_resistance
  have connected := (res_ne_top_iff_conn n (closedConfiguration n)).mp finite_resistance
  simpa using connected

/-- Embed a reduced replacement tree into the DHL, closing the unused branch of a series cell. -/
def treeConfiguration : (n : ℕ) → RConf n → Conf n
  | 0, _ => true
  | n + 1, Sum.inl descendants =>
      (treeConfiguration n descendants.1, treeConfiguration n descendants.2,
        closedConfiguration n, closedConfiguration n)
  | n + 1, Sum.inr descendants =>
      (treeConfiguration n descendants.1.1, treeConfiguration n descendants.1.2,
        treeConfiguration n descendants.2.1, treeConfiguration n descendants.2.2)

@[simp] theorem treeConfiguration_connection :
    ∀ (n : ℕ) (tree : RConf n), conn n (treeConfiguration n tree) = true
  | 0, _ => rfl
  | n + 1, Sum.inl descendants => by
      simp [treeConfiguration, conn_succ, treeConfiguration_connection]
  | n + 1, Sum.inr descendants => by
      simp [treeConfiguration, conn_succ, treeConfiguration_connection]

/-- Reduction of the concrete embedded network recovers the original replacement tree. -/
@[simp] theorem Phi_treeConfiguration :
    ∀ (n : ℕ) (tree : RConf n), Phi n (treeConfiguration n tree) = tree
  | 0, tree => by
      change Unit at tree
      cases tree
      rfl
  | n + 1, Sum.inl descendants => by
      simp [treeConfiguration, Phi, Phi_treeConfiguration, rinl]
  | n + 1, Sum.inr descendants => by
      simp [treeConfiguration, Phi, Phi_treeConfiguration, rinr]

/-- The genuine finite network obtained from unit edges by series and diamond replacements. -/
def treeNetwork : (n : ℕ) → RConf n → TTN
  | 0, _ => TTN.edgeTTN
  | n + 1, Sum.inl descendants =>
      TTN.seriesTTN (treeNetwork n descendants.1) (treeNetwork n descendants.2)
  | n + 1, Sum.inr descendants =>
      TTN.parTTN
        (TTN.seriesTTN (treeNetwork n descendants.1.1) (treeNetwork n descendants.1.2))
        (TTN.seriesTTN (treeNetwork n descendants.2.1) (treeNetwork n descendants.2.2))

/-- The direct series/diamond network and its DHL embedding have the same effective resistance. -/
theorem treeNetwork_effRes_eq_res : ∀ (n : ℕ) (tree : RConf n),
    (treeNetwork n tree).effRes = res n (treeConfiguration n tree)
  | 0, _ => by simp [treeNetwork, treeConfiguration, TTN.effRes_edge]
  | n + 1, Sum.inl descendants => by
      simp [treeNetwork, treeConfiguration, res_succ, TTN.effRes_series,
        treeNetwork_effRes_eq_res]
  | n + 1, Sum.inr descendants => by
      simp [treeNetwork, treeConfiguration, res_succ, TTN.effRes_series, TTN.effRes_par,
        treeNetwork_effRes_eq_res]

/-- The resistance recursion is the actual effective resistance of the finite replacement network. -/
theorem treeNetwork_toReal_effRes (n : ℕ) (tree : RConf n) :
    (treeNetwork n tree).effRes.toReal = Rres n tree := by
  rw [treeNetwork_effRes_eq_res, toReal_res_eq_Rres n (treeConfiguration n tree)
    (treeConfiguration_connection n tree), Phi_treeConfiguration]

end
end Cluster
