import RequestProject.Outlook.Matrices
import RequestProject.Outlook.EigenM
import RequestProject.Outlook.EigenN
import RequestProject.Outlook.Dimensions

/-!
# Subsection 4.2 of *Iterated Graph Systems (I)* — the mean matrices and their Perron roots

Aggregator for the formalisation of the computational content of Subsection 4.2 (arXiv:2603.13798),
"Outlook: Brownian spectral dimensions for the critical percolation cluster of the DHL":

* `Outlook.Matrices` — the mean offspring matrix `E(M)` and the mean boundary matrix `E(N)`, the
  reduction of their eigenvalue problems to the live blocks, and the characteristic polynomials of
  those blocks;
* `Outlook.EigenM` — `λ(E(M)) = 7 - 2√5 + √(73 - 32√5) ≈ 3.7303` is the spectral radius of `E(M)`;
* `Outlook.EigenN` — `λ(E(N)) = 2` exactly;
* `Outlook.Dimensions` — `log λ(E(M)) / log 2 = log λ(E(M)) / log λ(E(N)) ≈ 1.8993`.

The remaining content of Subsection 4.2 is conjectural (the dimension identities themselves, the
walk dimension, and the spectral-dimension conjecture) and is not formalized.
-/
