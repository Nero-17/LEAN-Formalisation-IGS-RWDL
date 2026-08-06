# §3.1 形式化说明与对原文命题的几点意见

本文件对应 `RequestProject/Section31/`（入口 `RequestProject/Section31.lean`），
形式化对象是 arXiv:2603.13798, *Iterated Graph Systems (I)*, §3.1
「Dirichlet form and diffusion limits」，外加 §3 开头它要用到的两条引理
（`GH_limit_metric`、`GHP_convergence`）。

遵循的原则正是你给的那条：**原文自己只是「引用」的深定理，一律写成显式假设；
原文自己论证的部分，逐条真证。** 全部文件编译通过，无 `sorry`，
只依赖 `propext`/`Classical.choice`/`Quot.sound`。

---

## 1. 逐条对照（证了什么）

| 原文命题 | 文件 | 这里真正证明的内容 |
|---|---|---|
| Lemma `GHP_convergence` | `Section31/CellMass.lean`（＋既有的 `Section3/Recursions.lean`） | 有限生点的层-`m` 星邻域质量 `≤ Cρ(N)^{m-k}·C'ρ(M)^{-m} → 0`，故 `μ({x})=0`；仿射递推与 `μ(Λ) ≍ ρ(M)^{-m}`（标量情形） |
| Lemma `sec31_trace_weighted` 的单胞元输入（Dirichlet 原理） | `Section31/DirichletPrinciple.lean` | 有限网络上的 Dirichlet 原理：给定边界值的能量极小元**存在且唯一**（紧性＋平行四边形恒等式），以及它唯一需要的解析输入——沿路径的离散 Poincaré 不等式 `(g x)² ≤ (L/c_min)ℰ(g)`（由 canonicality 提供路径） |
| Lemma `sec31_trace_weighted` | `Section31/TraceMin.lean` | 「胞元解耦」：层-`(n+1)` 能量在所有延拓上的最小值 = 各胞元最小值之和，且极小元唯一；以及重整化恒等式 `ρ(Ψ)^{n+1}ψ_i(v)^{-1} = ρ(Ψ)^n[v]_i^{-1}`（即特征方程 `Ψ(v)=ρ(Ψ)v` 恰好使 trace 保持共形） |
| Lemma `sec31_continuous_harmonics` | `Section31/HarmonicSplines.lean` | 由一致收缩 `θ<1` 得振幅 `osc_n ≤ θ^n osc_0`；紧空间上几何式 Cauchy ⟹ 一致收敛到连续函数；极大值原理 ⟹ 样条在 `C(Ξ_M)` 中一致稠密 |
| Lemmas `sec31_projection_tail_*` | `Section31/ProjectionTail.lean` | 调和投影的 Pythagoras 恒等式；几何级数求和给出 `‖u-u_m‖₂² ≤ C(ρ(M)ρ(Ψ))^{-m}ℰ(u,u)`（含显式常数 `C/(1-√q)²`） |
| Lemma `sec31_speed_measure` | `Section31/SpeedMeasure.lean` | `π_n(V(Λ)) ≤ C ρ(M)^{-m}`，常数显式且**与 `m` 无关**；弱极限的转移（`μ_{Ξⁿ} ⇒ μ` 且检验函数上差趋于 0 ⟹ `π_n ⇒ μ`） |
| Lemma `sec31_discrete_harmonics` | `Section31/DiscreteHarmonics.lean` | trace 电导的 Perron 渐近极限；**极小元的连续依赖**（一致收敛的二次型族在紧空间上的极小元收敛到唯一极小元）——这是该引理的数学核心；能量与 `L²` Gram 矩阵的收敛 |
| Theorem `sec31_mosco` | `Section31/Mosco.lean` | Mosco 收敛在 Kuwae–Shioya「变空间」意义下的定义（强/弱收敛作为参数）；liminf 不等式的收尾步骤（形式闭性 ⟹ `ℰ_W(f,f) ≤ liminf`） |
| Lemma `sec31_one_step_stay` | `Section31/ExitTime.lean`, `Section31/Main.lean` | `E[τ] ≤ t + E[(τ-t)^+]`（真的用测度论证明）＋ 由两侧退出时间界得到 `p_stay = c_exit/(2C_exit)` |
| Theorem `sec31_discrete_eld_tightness` | `Section31/ExitTime.lean` | 链论证中半径的两条标度恒等式：取 `δ=(t/r)^{1/(d_w-1)}` 时 `r·δ^{d_w-1}=t`，且增量个数 `r/δ = (r^{d_w}/t)^{1/(d_w-1)}`——后者正是结论指数中的量 |
| Corollary `sec31_continuous_stay` | `Section31/Main.lean` | 完整推导：离散停留估计 ＋ Skorokhod 耦合 ⟹ 极限扩散 `P_x(τ_{B(x,r)}>t_r) ≥ p_stay` |

## 2. 留作黑箱的（与原文引用一一对应）

Gromov–Hausdorff(–Prokhorov) 极限空间与拓扑；弱极限测度的存在性；
正则 Dirichlet 形式 ↔ Hunt 过程；变空间上 Mosco 收敛 ⟹ 过程收敛
（Kuwae–Shioya）；Azuma–Hoeffding 与 Aldous 胎紧准则；Skorokhod 表示定理；
单个规则图上两端点有效电阻的**取值**（§2 / Kigami；注意极小元的存在唯一性已在
`Section31/DirichletPrinciple.lean` 中真证，黑箱只剩「最小能量 = `c_n(e)(f(a)-f(b))²`」这一条）。

## 3. 我认为原文需要补条件或值得注意的地方

以下不是「结论错了」，而是**陈述里缺了一个条件**或**论证一步偏快**。

1. **Lemma `sec31_continuous_harmonics` 的一致收缩 `θ<1`（最值得注意的一条）。**
   原文说：对每个规则图与紧族中的每个电导向量，`0`–`1` 调和轮廓的
   *边振幅严格小于 1*，由规则图有限得到一致的 `θ∈(0,1)`。
   但若某个规则图 `R_i` 含有一条**直接连接两个种植点 `β_i^+`、`β_i^-` 的边**
   （"捷径边"），那么 `0`–`1` 调和轮廓在这条边的两端取值恰为 `0` 与 `1`，
   其边振幅等于 `1`，不可能 `<1`；相应的子胞元不发生任何收缩。
   标准假设（Assumption `ass:standing`）里，`K=1` 时明确要求
   `d(β_1^+,β_1^-) ≥ 2`（正好排除捷径边），但 `K≥2` 时只要求
   distance-positivity 与 `N` 本原，似乎并未排除某个 `R_i` 有捷径边。
   具体的反例结构：取 `K=2`，`R_1` = 一条 `β_1^+`—`β_1^-` 的 2 色直边 ＋ 一条经过内点的
   长度 2 的路径；`R_2` = 长度 2 的路径。这个系统是 canonical 的，
   且因为 `K=2>1` 不受「`K=1` 时 `d(β^+,β^-)≥2`」这一限制，
   distance-positivity 也满足，但 `R_1` 的 `0`–`1` 调和轮廓在那条直边上振幅恰为 `1`。
   好消息是：**结论应该仍然成立**，只是证明要改成「多层收缩」——那条直边在下一层会被
   `R_2` 替换，其子胞元振幅降为 `1/2`，因此存在固定的 `p` 使得「每 `p` 层收缩 `θ<1`」，
   具体地可取 `θ' = θ^{1/p}` 重新参数化。建议在 §3.1 里要么显式排除「规则图含连接两个
   种植点的边」，要么把收缩改成多层版本。形式化里这一点是显式假设：
   `osc_le_geometric` 以 `θ` 为参数，`θ<1` 由使用者提供，
   而 `exists_continuous_limit_of_geometric` 只需要「相邻项距离几何衰减」，
   多层收缩同样适用。

2. **`ρ(M)ρ(Ψ)>1` 在 Lemma `sec31_projection_tail_*` 中是必需的。**
   `C(ρ(M)ρ(Ψ))^{-m}` 只有在 `ρ(M)ρ(Ψ)>1`（等价于游走维数 `d_walk>0`）时
   才随 `m` 衰减，也才能推出 Theorem `sec31_limit_dirichlet_form` 里所要的
   可闭性与紧嵌入。原文在 §3.1 未把它列为条件（§3.2 才假设 `ρ(Ψ)>1`）。
   形式化里它是 `projection_tail_sq_bound` 的显式假设 `q<1`。

3. **Theorem `sec31_discrete_eld_tightness` 需要 `d_walk>1`。**
   指数 `1/(d_walk-1)` 与半径取法 `δ=(t/r)^{1/(d_walk-1)}` 只有在 `d_walk>1`
   时有意义（`d_walk=1` 时链论证退化）。这在 EIGS 的例子里都成立，
   但作为陈述应写出来。形式化中 `radial_step_time`、`radial_step_count`
   都以 `1<dw` 为假设。

4. **Lemma `sec31_trace_weighted` 中「极小元唯一」。**
   只有当每个规则图的内部顶点都与两个种植点电连通时才成立（否则孤立部分上
   常值任取，能量同为 0）。这由标准假设中的 canonicality
   （每条边都落在连接 `β^+`、`β^-` 的某条简单路径上）保证，
   所以结论没问题，只是原文「strict convexity gives uniqueness」一句
   隐含用了 canonicality，值得点明。形式化里唯一性以「每个胞元的极小元唯一」
   为假设（`eq_of_minimises_energy`）。

5. **Lemma `sec31_speed_measure` 的常数。**
   原文写「对每个 `m` 存在 `C_m`」。按它自己给的三条估计
   （`|E(Λ)|≍ρ(M)^{n-m}`、`|E(Ξⁿ)|≍ρ(M)^n`、`deg(u_i)≲ρ(N)^{n-m}`，且
   `ρ(N)≤ρ(M)`）实际可以取**与 `m` 无关**的常数；
   `stationary_measure_cell_le` 给出的就是这个更强的版本。

6. **Theorem `sec31_mosco` 的 limsup 半部分。**
   原文说「调和样条是 core，故完整的 limsup 成立」。从 core 上的 recovery
   序列过渡到整个定义域需要一次对角线（Attouch 型）选取，这一步没有写；
   它是标准的，但不是一行。形式化里 `mosco_of_recovery_on_core` 把这一步
   的产物（对每个 `u` 都有 recovery 序列）作为假设列出，从而使得缺口显式可见。

7. **Theorem `sec31_ghps` 的去 Poisson 化。**
   由 `sup_{t≤T}|N_{a_nt}-a_nt|/a_n → 0` 推出离散时间版本，还需要极限过程的
   路径正则性（`W` 连续）配合 Skorokhod 拓扑的时间变换；原文一句带过，
   结论标准且正确，只是论证略快。

---

**一句话总结**：§3.1 在「引用当假设」的前提下是可以形式化的，
而且原文属于自己的推理（解耦、收缩、几何级数、Perron 渐近、极小元连续性、
停留概率、标度恒等式、耦合传递）都已在 Lean 里真证；
需要补的只是上面几条隐含条件，其中第 1 条（捷径边）是最实质的一条。

---

# 附录（后续 run）：第 3 条意见第 1 点已解决——标准假设本身排除了「捷径边」

你指出「我们的设定里不存在捷径边，可以看文章的基础 assumption」。**你是对的**，
而且现在这一点已经在 Lean 里从假设变成了定理。理由与形式化如下。

## 1. 为什么标准假设排除捷径边

Assumption `ass:standing`(2) 有两句话，恰好覆盖两种情形：

* **`K ≥ 2`（distance-positivity）。** `𝒟` 是路径选择族：对每个规则图 `R_i`
  选定一条 `β_i^+`–`β_i^-` 的简单路径后，矩阵的 `(i,j)` 元是该路径上颜色-`j` 边的条数；
  distance-positive 要求 `𝒟` 中**所有**矩阵都是正的，即**任何**可选路径都要用到**每一种**颜色。
  若 `R_i` 有一条直接连接两个种植点的边，则「这条单边」本身就是一条可选路径，
  其颜色向量是单点 `{c}`，当 `K ≥ 2` 时缺掉了别的颜色，与正性矛盾。
* **`K = 1`。** 假设里直接写了 `d(β_1^+,β_1^-) ≥ 2`，一条捷径边会让距离等于 `1`。

形式化：`RequestProject/Section31/NoShortcut.lean` 中的
`no_shortcut_of_distance_positive` 与 `no_shortcut_of_two_le_dist`。
（因此原注记里那个「`K=2` 反例」是不成立的：`R_1` 里那条 2 色直边是一条可选路径，
其颜色向量只含一种颜色，破坏了 distance-positivity。）

## 2. 由「无捷径边」真正证出 `osc < 1` 与一致 `θ < 1`

`RequestProject/Section31/Oscillation.lean` 从零证明了下面这条链
（原文只是断言「边振幅严格小于 1」）：

1. `grad_eq_zero_of_min`：能量极小元在内部顶点满足 Euler–Lagrange 方程
   （沿 `g + tδ_x` 求导，二次函数的一次项必须为零）；
2. `energy_clamp_le` + `range_subset_of_min`：截断不增能量，配合极小元唯一性
   得到极大值原理 `0 ≤ g ≤ 1`；
3. `grad_lt_zero_of_zero_at`：强极大值原理——若 `g ≥ 0`、`g(x)=0` 而 `x` 有一个
   取正值的邻点，则 `grad g x < 0`，故 `x` 不可能是内部点；
4. `mem_of_osc_one`：于是振幅恰为 `1` 的边，两个端点都必须是种植点；
5. `edge_osc_lt_one_of_no_shortcut`：**无捷径边 ⟹ 每条边的振幅 `< 1`**；
6. `energy_affine`、`min_affine`、`edge_osc_le_mul_of_profile`：极小元对边界数据仿射，
   于是 `< 1` 变成「子胞元振幅 `≤ θ ×` 父胞元振幅」。

`RequestProject/Section31/Contraction.lean` 把这些拼成
`uniform_contraction_of_no_shortcut`：对有限个（规则图，电导向量）对，
存在统一的 `θ ∈ [0,1)` 使得所有边界数据的调和延拓都满足上述收缩；
再接 `exists_continuous_limit_of_contraction` 得到 `osc_n ≤ θ^n osc_0`
与紧空间上的连续极限。电导向量取自紧族（`α^{(q)} → α^{(∞)}`）这一情形由
`exists_uniform_lt_one_of_tendsto` 处理，其收敛性输入正是既有的 `tendsto_minimiser`。

`RequestProject/Section31/PathExample.lean` 在最短的合法规则图（长度 2 的路径）上
逐条验证了上述所有假设：其 `0`–`1` 轮廓为 `(0, 1/2, 1)`，`θ = 1/2`，
以此确认这些命题不是空洞成立的。

## 3. 顺带补上的一条

Theorem `sec31_limit_dirichlet_form` 里「Markov 性由有限 trace 继承」这句，
现在也真证了：`RequestProject/Section31/MarkovProperty.lean` 的
`energy_comp_le_of_lipschitz`（任意正规压缩 `T` 满足 `ℰ(T∘g) ≤ ℰ(g)`）与
`markov_of_iSup`（上确界保持 Markov 性）。

## 4. 仍然保留的意见

上面第 2–7 条（`ρ(M)ρ(Ψ)>1`、`d_walk>1`、唯一性用到 canonicality、
speed measure 常数可与 `m` 无关、Mosco 的对角线选取、去 Poisson 化）不变；
只有第 1 条现在应读作：**结论无需补条件，标准假设已经蕴含它**，
上面给出的就是那条被原文省略的论证。

---

# 附录（第三轮）：Lemma 3.11 的概率论证

这一轮把 Lemma 3.11 证明里「Uniform exit bound for cells」那一段的概率部分
从假设变成了定理。相关文件：`Section31/WatchedChain.lean`（有限状态链的一般
工具与骨架跳数估计）、`Section31/TraceChain.lean`（watched chain 的构造）、
`Section31/TraceDecomposition.lean`（optional stopping 的分解）、
`Section31/WatchedChainExample.lean`（非空性检验）。

## 1. 框架：不需要测度论

`FinChain S` 就是有限状态空间上的转移矩阵。生存概率 `notHit ch B k z = P_z(σ_B > k)`
按一步递推定义，期望击中时刻定义为截断期望的上确界
`hitTime ch B z = ⨆_K ∑_{k<K} P_z(σ_B > k)`（即 `E_z[σ_B]`，单调收敛）。
累积代价 `costLim ch B d z = ⨆_k E_z[∑_{j<min(σ_B,k)} d(Z_j)]`。
这样整段论证是纯粹的实分析＋有限和，避免了在 Lean 里构造路径空间上的测度。

## 2. 「期望跳数 ≤ C_R」：给出了显式常数

原文说「由 Corollary 2.8，这些电导落在 `(0,∞)^K` 的一个固定紧集里，
所以期望跳数至多是只依赖 EIGS 的常数 `C_R`」。这里把它证成：

* `notHit_le_of_descent`：若每个非终端点都有一条概率 `≥ p` 的边使某个「到终端的
  距离」`ν` 严格下降，则 `P_z(σ_B > k) ≤ 1 - p^k`（只要 `ν z ≤ k`）；
* `partialHit_le_of_uniform_hit`：`N` 步内以概率 `≥ ε` 命中 ⟹ `E_z[σ_B] ≤ N/ε`
  （按长度 `N` 的段做几何衰减，再对几何级数求和）；
* `condChain_expected_jumps_le`：对电导落在 `[a,b]` 的电导游走，
  `p ≥ a/(|S|·b)`，于是 **`C_R = N (|S| b / a)^N`**。

这个常数确实只依赖于规则图（`|S|`、`N`）与电导的紧区间 `[a,b]`——这正是
「紧电导族给出一致的 `C_R`」这句话的内容。代价是它对 `N` 是指数的；
原文只说「一个常数」，没有给形状，所以两者不矛盾。

## 3. watched chain 真的是马氏链

`TraceChain.lean` 里把骨架的击中分布 `P_v(X_{σ_S} = w)` 造出来（`hitDistLim`，
`k` 步击中分布的单调极限），证明它支撑在 `S` 上、总质量 `= 1 - P_v(σ_S > k) → 1`，
从而当骨架被几乎必然击中时（有限状态空间上由第 2 条的一致估计保证，见
`tendsto_notHit_zero_of_uniform_hit`）得到一个真正的转移核

  `Q(v,w) = ∑_u P(v,u) · P_u(X_{σ_S} = w)`，即 `traceChain`。

注意：这里的 trace 链允许在同一个骨架点上「原地」跳（即 `Q(v,v) > 0`），
而原文说的是「在相继**不同**的骨架点观察」。两者的期望跳数只差一个有界因子，
而且本文的估计对带自环的链同样成立（descent 假设只要求存在一条使 `ν` 下降的边），
所以结论不受影响。

## 4. optional stopping：分解式是证出来的，不是假设

`exit_time_le_skeleton_add_cost`：对任意有限链、骨架 `S`、终端集 `B`，

  `E_z[σ_B] ≤ E_z[σ_S] + ∑_w P_z(X_{σ_S}=w) · (从 w 出发 watched chain 累积的跳时)`，

从而 `E_z[σ_B] ≤ R_S + D·C_R`。证明不用强马氏性，而是把右端

  `g(v) = E_v[σ_S] + ∑_w P_v(X_{σ_S}=w) h(w)`

验证成击中方程的**超解**（`g ≥ 1 + Pg` 在 `B` 外），再用
`hitTime_le_of_supersolution`。三处细节：
`v ∉ S` 时用 `E_v[σ_S]` 与 `P_v(X_{σ_S}=·)` 的一步递推（都要把上确界与有限和交换，
这靠单调有界收敛）；`v ∈ S\B` 时用 `costLim` 自身是 trace 链的超解
（`costLim_supersolution`）；最后 `∑_w P_z(X_{σ_S}=w) ≤ 1`。

于是 `cell_exit_recursion_of_conductance_skeleton` 给出

  `E_z[σ_B] ≤ T_{s-1} + C_⋆ q^{s-1} · C_R`，

其中仍作输入的只有三样，与原文引用一一对应：
(i) `T_{s-1}` 界住到骨架的期望时间（即上一层的归纳假设）；
(ii) 一次 excursion 的期望时长 `≤ C_⋆ q^{s-1}`（Lemma 2.22）；
(iii) trace 核 `Q` 等于规则图上的电导游走、其电导落在固定紧区间
（Lemma 2.4 的 super-edge reduction ＋ Corollary 2.8）。
再配合已有的 `geometric_recursion_bound` 展开，就得到 `T_s ≤ C_T q^s`。

## 5. 非空性

`WatchedChainExample.lean` 在最短骨架（路径 `0—1—2`，终端 `{0,2}`，全部电导为 1）上
逐条验证了上述所有假设：`C_R = 3`（真值 1），单位跳时下累积代价恰为 `1`；
并且把骨架取成全体顶点后，`exit_time_le_skeleton_add_cost` 的四条假设
（骨架几乎必然被击中、到骨架的时间一致有界、excursion 一致有界、trace 核＝电导游走）
也同时被验证，给出 `E_z[σ_B] ≤ 6`。所以这两条定理都不是空洞成立的。
