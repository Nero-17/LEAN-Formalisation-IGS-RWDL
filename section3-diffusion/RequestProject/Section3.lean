import RequestProject.Section3.SpectralDimension
import RequestProject.Section3.Recursions
import RequestProject.Section3.OnDiagonalLower
import RequestProject.Section3.ResistanceForm
import RequestProject.Section3.ConditionalMain
import RequestProject.Section3.DHL

/-!
# A conditional formalisation of Section 3 of arXiv:2603.13798

*Iterated Graph Systems (I): random walks and diffusion limits*, Section 3
("Diffusion limits and Brownian motion"), formalised in the style
"deep analytic inputs are explicit hypotheses, the paper's own arguments are
proved".

| file | paper |
|---|---|
| `Section3.Recursions` | Lemma "GHP_convergence" (scalar Perron recursion, cell mass `≍ ρ(M)^{-m}`), Lemma "sec32_point_boundary" (the contraction `A_{L+1} ≤ ρ(Ψ)^{-1} A_L + B`), Proposition "final_recurrent" (algebraic part) |
| `Section3.ResistanceForm` | Theorem "sec32_resistance_metric" (existence of the limit of the compatible traced energies), Lemma "sec32_common_core" (uniform decay of the harmonic-spline error) |
| `Section3.OnDiagonalLower` | Theorem "general-lower" (Cauchy–Schwarz on a ball) |
| `Section3.SpectralDimension` | the limit computation behind Theorem "diffusion-spectral", including the case with a logarithmic correction |
| `Section3.ConditionalMain` | Theorem "diffusion-heat" as data, Theorem "diffusion-spectral" as a conditional theorem |
| `Section3.DHL` | the DHL example: exponents `1` and `2`, plus a non-vacuity instance |

Left as black boxes (they are the inputs the paper itself imports from Kigami,
Fukushima et al. and Kuwae–Shioya, and are *not* proved here): the Gromov–Hausdorff
limit space, the weak limit measure, the regular Dirichlet form and its Mosco
limit, the resistance form and its completion, the existence and joint continuity
of the heat kernel, and the two-sided on-diagonal estimates themselves.
-/
