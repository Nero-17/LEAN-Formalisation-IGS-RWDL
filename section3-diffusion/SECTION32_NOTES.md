# §3.2「Resistance-form Brownian motion」形式化笔记

对应目录：`RequestProject/Section32/`，入口 `RequestProject/Section32.lean`。
原则与 §3.1 相同：**论文自己只是引用文献的深定理，一律写成显式假设；论文自己论证的部分，逐条真证**。
全部文件编译通过、无 `sorry`、只依赖 `propext` / `Classical.choice` / `Quot.sound`。

## 1. 真正证明了什么

| 论文 | 文件 / 定理 |
|---|---|
| `R_{m+1}=R_m` on `V(Ξ^m)`，因而 `R_*` 良定义 | `TraceResistance.condEnergy_succ_eq`、`Reff_stable`、`Reff_eq_of_mem` |
| `ℰ_𝒱(f,f)=lim_m ℰ_m^W` 存在（单调有界） | `TraceResistance.traced_energy_tendsto`（配合 `Section3.ResistanceForm.tendsto_traced_energy`） |
| Lemma `sec32_point_boundary` 的完整归纳 | `PointBoundary.point_boundary`（常数显式 `C_∂ = max(A₀, Bρ/(ρ-1))`）、`point_boundary_tendsto` |
| 该引理的非空实例（二进模型） | `DyadicExample.pointBoundaryHyp_dyadic`、`dyadic_point_boundary` |
| Theorem `sec32_resistance_metric` 的拓扑部分 | `ResistanceHomeo.uniformContinuous_of_cell_bound`（胞元界 ⟹ 一致连续 ⟹ `d`-收敛列是 `R_*`-Cauchy，且极限与逼近列无关）、`iota_surjective`、`iota_injective`、`resistanceHomeo` |
| Lemma `sec32_common_core` 两半 | `CommonCore.spline_core_dense`（正交补平凡 ⟹ 稠密）、`spline_error_pointwise` / `spline_error_L2_le` / `spline_error_L2_tendsto` |
| Theorem `sec32_brownian_motion` | `FormsAgree.closed_forms_agree`（公共 core 上相等的两个闭形式处处相等）、`process_eq_of_forms_agree` |

## 2. 仍作黑箱的（与论文引用一一对应）

* 由相容有限 trace 构造电阻形式，并认定其电阻度量恰为 `R_*`（Kigami）；
* 有限能量函数在电阻度量下连续（Kigami）；
* trace 理论：level-`m` 样条子空间的 `ℰ_R`-正交补 = 在 `V(Ξ^m)` 上迹为零的函数；
* 正则 Dirichlet 形式 ↔ 对称 Hunt 过程，以及由此得到的半群、热核相等（Fukushima 等）；
* level-`m` 胞元两端点之间的电阻 `ρ(Ψ)^{-m}[v]_i`（§2），以及 `(ℰ_m^W)` 的 trace 相容性本身（Lemma `sec31_trace_weighted`，其分解见 `Section31/TraceMin.lean`）。

每一条都是某个已命名定理的显式假设，因此「缺口在哪里」是可见的。

## 3. 对原文陈述的几点意见

1. **Lemma `sec32_point_boundary` 的 `A_L` 先验可能是 `+∞`。**
   原文先定义上确界 `A_L`，再写「Assume that `A_L < ∞`」并推出 `A_{L+1} ≤ ρ(Ψ)^{-1}A_L + B`。
   这在逻辑上要补一句归纳（`A_0 < ∞` 且递推保持有限），结论才成立。
   形式化里绕开了这一点：直接对显式常数 `C_∂ = max(A₀, Bρ/(ρ-1))`（即递推的不动点）做归纳，
   不需要先谈 `A_L` 是否有限。
2. **该引理只对 `z ∈ 𝒱` 成立，不能推广到 `𝒱^∞`。**
   证明用的是「`z` 在某个 `m+ℓ` 层后代胞元里成为端点」，即 `h_Λ(z) < ∞`；
   无限生点没有这个性质。原文陈述里 `z ∈ 𝒱 ∩ Λ` 已经排除了它，但值得点明：
   形式化中 `point_boundary` 的结论按高度 `L` 分层给出，`point_boundary_tendsto` 明确要求 `∃ L, h_Λ(z) ≤ L`。
3. **Theorem `sec32_resistance_metric` 的单射性一步有一个隐含步骤。**
   原文用「有限能量函数在电阻度量下连续，故 `u` 连续延拓到 `Ξ_R`」得出 `ι(x) ≠ ι(y)`。
   要真正得到这一点，还需要延拓 `ũ` 满足 `ũ ∘ ι = u` **在整个 `Ξ_M` 上**，
   这由 `𝒱` 稠密加两边连续给出，原文没写。形式化里 `iota_injective` 把「`ũ ∘ g = u|_𝒱`」列为假设，
   再用稠密性把它提升到 `ũ ∘ ι = u`（这一步是真证的）。
4. **`R_*` 满足三角不等式是引用来的，不是显然的。**
   §3.2 多处（尤其 Lemma `sec32_point_boundary`）用到 `R_*` 的三角不等式；
   对电阻度量而言这不是平凡事实（需要 Kigami 的电阻形式公理或单位流论证）。
   形式化中它是 `PointBoundaryHyp.tri`，与论文引用 Kigami 的位置一致。
5. **Lemma `sec32_common_core` 的 `L²` 收敛用到 `μ` 有限。**
   由 `sup`-界推 `L²`-界需要 `μ(Ξ_M) < ∞`；这里 `μ_{Ξ_M}` 是概率测度，所以没问题，
   形式化中写成 `[IsProbabilityMeasure mu]`。
6. **「两个闭形式在公共 core 上相等 ⟹ 处处相等」需要把定义域也对上。**
   形式化 `closed_forms_agree` 采取的读法是：两个形式定义在同一个向量空间 `F` 上，
   core `D ⊆ F` 对二者都是 core（每个元素都有形式范数 + `L²` 双重逼近列），
   且二者都是闭的（Fatou）。在这个读法下结论是真证的。
   若只知道「同一族样条分别是两个形式的 core」，还需要先说明两个定义域一致，
   而那一步用的正是同一个 Fatou 论证，原文一句「hence agree everywhere」带过。
7. **`d_R(Ξ)>0`（即 `ρ(Ψ)>1`）在本节是必要的，不只是方便。**
   它同时被用于：`A_{L+1} ≤ ρ⁻¹A_L+B` 的收敛、`ρ(Ψ)^{-m} → 0`（`ι` 的一致连续性与
   样条误差趋零）。形式化中每处都以假设 `1 < rho` 出现，不可省略。

## 4. 非空性

抽象假设最怕真空成立。`DyadicExample.lean` 在线的二进模型（胞元 = 二进区间、
`R(x,y)=|x-y|`、`ρ=2`、`A₀=B=1`）里逐条验证了 `PointBoundaryHyp` 的全部字段，
并由 `point_boundary` 得到 `|z-a_Λ| ≤ 2·2^{-m}`（真值为 `2^{-m}`，常数 `C_∂=2` 正是公式给出的值）。
