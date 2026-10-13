# Summary of changes for run 41badc4e-37e0-4b78-a4c9-8d26db277ba0
已完成 Prop 4.2 的形式化（按您选择的方案一：单一耦合，而非把逐层边缘分布拼起来）。

**结果**

1. **过程形式的 Prop 4.2**（`RequestProject/Cluster/Coupling.lean`，`Cluster.cluster_resistance_process`）：在临界参数处，条件于两个边界点连通时，钻石分层格上渗流团簇沿各层的电阻序列，与 4.1 节约化过程 (R_0,…,R_n) 同分布。按有限窗口给出（对每个 n，窗口 (R_0,…,R_n) 的联合分布相等），这确定了过程的分布，且避免了无穷维路径空间。

2. 由它重新导出原来的逐层版本 `Cluster.cluster_resistance_law_of_process`，与既有的 `Cluster.cluster_resistance_law` 一致。

**新增的三块内容**

- `RequestProject/Cluster/Coarse.lean`：粗粒化映射 `coarse n : Conf (n+1) → Conf n`（第 n 层的一条边为开，当且仅当替换它的钻石连通其两端），证明它保持端点连通性（`conn_coarse`），并且**在 p_c 处保测**（`confMeasure_map_coarse`，用到不动点关系 2p_c²−p_c⁴=p_c）——这正是把各层拼成一个过程的耦合。
- `RequestProject/Cluster/Tree.lean`：把 4.1 节的约化过程实现为深度 n 的“替换选择树” `RConf`，带电阻 `Rres`、截断 `rtrunc`、分布 `rMeasure` 和窗口 `rwin`；`rMeasure_map_Rres` 说明它与 4.1 节的 `lawMeasure` 相容。
- `RequestProject/Cluster/Coupling.lean`：约化映射 `Phi n : Conf n → RConf n`（两支都连通⇒钻石胞元；恰一支连通⇒串联胞元，删去悬挂部分），三条关键性质：`rtrunc_Phi`（Φ 与一步替换/粗粒化交换，这是唯一的归纳步骤）、`toReal_res_eq_Rres`（Φ 保持电阻）、`Phi_pushforward`（Φ 把条件化的渗流测度推前为约化树的分布）。

**验证**：`lean_build` 全项目通过；`RequestProject/` 中无 `sorry`/`admit`/`axiom`；主定理的公理依赖仅为 `propext, Classical.choice, Quot.sound`。电阻始终是开团簇网络真正的 Thomson 有效电阻，而非手写递推。

`FORMALIZATION.md` 已更新（新增“Proposition 4.2 as an identity of processes”一节），`ARISTOTLE_SUMMARY.md` 未改动。所有工作已提交并推送。

# Summary of changes for run 35f1b1a0-9dfe-4cad-b3e1-20a7a6ea34c9
可以，4.2 节的两个矩阵特征值以及由此得到的 1.8993 现在都已机器验证完毕。全工程 `lake build` 通过，新增内容无 `sorry`/`admit`/`axiom`，主定理仅依赖标准公理（`propext`、`Classical.choice`、`Quot.sound`）。

新增目录 `RequestProject/Outlook/`（聚合文件 `RequestProject/Outlook.lean`），方法与你说的一致：**先做特征多项式的因式分解，再用"存在唯一性 + 区间算术"定位特征值**。

## 1. 矩阵与特征值框架（`Outlook/Matrices.lean`）
- 按论文原样写下四色系统的 `4×4` 平均后代矩阵 `E(M)` 与 `8×8` 平均边界矩阵 `E(N)`（颜色序 红-蓝-绿-黑），以及它们的活跃块 `EMlive`(3×3)、`ENlive`(6×6)，和把 `ENlive` 按奇偶下标拆开的两个 `3×3` 块 `ENodd`、`ENeven`。
- 特征值取初等定义 `HasEig A z ↔ ∃ v ≠ 0, A *ᵥ v = z • v`（等价于 `det (z•1 − A) = 0`），谱半径 `specRad A = sSup {‖z‖ : z 是特征值}`。
- 证明了黑色（墓地）行列只贡献特征值 `0`：`hasEig_EM_live`、`hasEig_EN_live`、`hasEig_ENlive_split` 及其反向的三条延拓引理；并在 `p² = 1 − p` 下算出三个 `3×3` 块的特征多项式：
  `det(t·1−EMlive) = (t−(4−4p))(t²−(10−8p)t+8p)`，
  `det(t·1−ENodd) = (t−2)(t²+(8p−6)t+(20p−12))`，
  `det(t·1−ENeven) = (t−2p)(t²+(6p−6)t+(8p−4))`。
- 配套引理 `quad_root_cases`：实系数首一二次式的复根要么是实根，要么模平方等于常数项——用来处理复特征值。

## 2. λ(E(M)) ≈ 3.7303（`Outlook/EigenM.lean`）
- 闭形式：`λ(E(M)) = (10 − 8p_c + √(164 − 256p_c))/2 = 7 − 2√5 + √(73 − 32√5)`（`lamM`、`lamM_eq`）。
- `lamM_hasEig`：它确实是 `E(M)` 的特征值（给出非零特征向量）；`hasEig_EM_norm_le`：任何复特征值的模 `≤ λ(E(M))`；于是 `lamM_isGreatest` / `specRad_EM`：它就是 `E(M)` 的谱半径。
- `lamM_unique`：它是**唯一**的、实的且 `≥ 2` 的特征值（另两个根约 1.5279、1.3254）。
- 区间算术：`3.7302885 < λ(E(M)) < 3.7302886`，故 `lamM_approx : |λ(E(M)) − 3.7303| < 10⁻⁴`。

## 3. λ(E(N)) = 2（`Outlook/EigenN.lean`）
- `two_hasEig_EN`：`2` 是 `E(N)` 的特征值（奇块的 Perron 根）；`hasEig_EN_norm_le`：所有复特征值模 `≤ 2`（奇块余下是一对模 `√(20p_c−12) ≈ 0.60` 的共轭复根，偶块的根为 `2p_c ≈ 1.236`、`≈1.7532`、`≈0.5386`）。于是 `lamN_isGreatest` / `specRad_EN`：谱半径**恰好等于 2**，不是近似值。

## 4. 由此的 1.8993（`Outlook/Dimensions.lean`）
- `dimBox = log λ(E(M))/log 2`，`dimDeg = log λ(E(M))/log λ(E(N))`；`dimDeg_eq_dimBox`（因为 λ(E(N)) = 2）。
- 对数部分同样用区间算术：把 `λ(E(M)) = 4(1−u)`（`u ≈ 0.0674`），用 `log(1−u)` 的五项 Taylor 余项估计配合 `λ(E(M))` 的区间与 Mathlib 的 `log 2` 十进制界，得到 `1.89928 < dimBox < 1.89929`（`dimBox_enclosure`），从而 `|· − 1.8993| < 10⁻⁴`（`dimBox_approx`、`dimDeg_approx`）。
- `section42_numerics` 把三条数值结论合并成一条总成定理。

## 范围说明
只形式化了 4.2 节的**计算性内容**。该节把这些商等同于极限簇的 box/degree 维数、以及 walk 维数与谱维数的部分，论文本身即为猜想，未形式化；另外 `dim_R = α/log 2 ≈ 0.8123` 与 `dim_W ≈ 2.7116` 依赖于 α ≈ 0.5631 这一**数值模拟估计**（论文用 population dynamics 得到，非严格界），因此不属于可机器验证的计算内容——4.1 节已严格证明的是 α 的存在性与 α(p_c) > 0。

`FORMALIZATION.md` 已新增一节完整记录以上内容（未改动 `ARISTOTLE_SUMMARY.md`）。所有工作已提交并推送。

# Summary of changes for run 312929dc-0a26-49ce-9223-ad1e798b8667
已完成 Proposition 4.2 的形式化，全部无 `sorry`，`lake build` 通过，主定理仅依赖标准公理（`propext`、`Classical.choice`、`Quot.sound`）。

新增/完成的内容（都在 `RequestProject/Cluster/` 下，聚合文件 `RequestProject/Cluster.lean`）：

1. `Cluster/Network.lean` — 从零构建有限**二端电网络** `TTN`（有限点集、有限边集、两个不同端点，单位电阻边）。用 Thomson 原理把有效电阻定义为单位流能量的下确界，取值在 `ℝ≥0∞`（`⊤` 表示两端不连通）。证明了：流的缩放律、单边电阻为 1、断开时为 `⊤`，以及两条结构定律
   - `TTN.effRes_series`：串联时电阻相加；
   - `TTN.effRes_par`：并联时电阻的倒数相加（含 `⊤` 的退化情形，因而"悬挂的断开分支自动不影响两端电阻"是自动成立的）。

2. `Cluster/DHL.lean` — 钻石分层格 (DHL) 上的**键渗流**：构型 `Conf n`（`Conf 0 = Bool`，`Conf (n+1)` 为四份拷贝）、开边构成的网络 `net n c`、其两端有效电阻 `res n c`、i.i.d. Bernoulli(p) 测度 `confMeasure p n` 及其像测度 `resLaw p n`。由上面两条电网络定律得到分布递推 `resLaw_succ`。

3. `Cluster/Law.lean` — 引入"电阻律" `IsResLaw ρ m λ`（`ρ = m·δ_⊤ + λ` 经 `ENNReal.ofReal` 的推前，`λ` 是集中在正实数上的有限测度），并计算它在串联 (`IsResLaw.sum`) 与并联 (`IsResLaw.par`) 下的变化（并联的两个交叉项恰好对应删去断开分支），以及"两条串联对的并联 = 四重 diamond 映射"的重排引理 `par_series_prod`。

4. `Cluster/Prop42.lean` — 临界计算。由 `p_c² = 1 − p_c` 得 `pdiamond p_c = p_c³`、`pseries p_c = 2p_c²`，再对 `n` 归纳得到：
   - `resLaw_isResLaw`：`resLaw p_c n` 的断开质量为 `1 − p_c`，有限部分为 `p_c ·` 约化电阻 `R_n` 的分布；
   - `prob_connected`：在每一层 `n`，两端点连通的概率恰为 `p_c`；
   - `cluster_resistance_law`（**Proposition 4.2**）：在两端点连通的条件下，第 `n` 层临界渗流簇的两端有效电阻的分布恰为 4.1 小节约化电阻 `R_n` 的分布 `lawMeasure (pdiamond p_c) (pseries p_c) n`。

说明（范围）：命题被形式化为**每一层 `n` 的分布相等**（一维边缘分布），与本项目对约化过程一贯采用的约定一致；原文把 Proposition 4.2 表述为整个**过程**的同分布，要把边缘结论提升为过程结论需要跨层的自顶向下耦合，这一步没有形式化。所涉电阻都是开簇的真实 Thomson 有效电阻，而非人为设定的递推。

`FORMALIZATION.md` 增加了一节记录以上内容与范围说明（未改动 `ARISTOTLE_SUMMARY.md`）。所有工作已提交并推送。

# Summary of changes for run 49052e9c-36c3-4d6a-87f5-220b0a79e6d3
完成了你要求的三点，全部机器验证通过（整个工程编译成功，无 sorry/admit/axiom/@[implemented_by]，三条新/改定理仅依赖标准公理 propext、Classical.choice、Quot.sound）。

## 第 3 点：把区段从 p_diamond ≤ 1/2 放宽到 p_diamond ≤ 1/√3
在 `RequestProject/Reduced/Cases23.lean` 新增逐点合并界 `E1Einv_le_of_sq`：在单一假设 `pd² ≤ 1/3` 下，对每个 n 都有 `E[R_n]·E[1/R_n] ≤ 11/5`。证明按 `pd ≤ 1/2`（用 `E1Einv_le`）与 `1/2 < pd`（用 `case2_inv … |>.2`）分情形，两支都不用单调性假设 `hmono`。

## 第 2 点：在具体定理中暴露 quenched = annealed 等式
在 `RequestProject/Reduced/JointSpace.lean` 改写 `reduced_quenched_exponent_concrete`：不再丢弃抽象定理的退火分量，而是保留它，并经 `integral_Rclamp` 把 `∫ R'_n dP` 改写为 `E1 pd ps n`（= E[R_n]），使该分量读作 `(1/n) log E[R_n] → α` 并加入结论。同时把假设 `hhalf : pd ≤ 1/2` 换成 `pd² ≤ 1/3`，把合并界喂给乘积矩假设 `hM`。临界点仍被覆盖（pdiamond pc < 1/2 ⟹ 平方 < 1/4 < 1/3）。

## 第 1 点：临界点的总成定理
新增 `RequestProject/Reduced/Critical.lean`，定理 `reduced_exponent_critical` 把三条结果（`reduced_quenched_exponent_concrete`、`reduced_annealed_exponent`、`alpha_pc_pos`）合并并在临界参数处实例化（P := jointMeasure (pdiamond pc) (pseries pc)，R_n := proj n）：存在确定常数 α，满足 0 < α ≤ log 2、log((14 − 4√5)/3) ≤ α，使得 P-几乎必然 (1/n) log R_n → α，同时 (1/n) log E[R_n] → α。两个 α 由极限唯一性（退火序列相同）识别为同一个。即：在 p_c 处淬火指数几乎必然存在、等于退火指数、且严格为正。

新文件已加入 `RequestProject/Reduced.lean` 的导入；`FORMALIZATION.md` 已相应更新（`ARISTOTLE_SUMMARY.md` 未改动）。

# Summary of changes for run 5839fed6-69f2-4b59-9d2c-8b76bfb0a701
我把 arXiv:2603.13798 第 4.1 小节中你指定的两条命题都形式化并机器验证完毕（全工程编译通过，无 sorry/admit/axiom/@[implemented_by]，两条主定理仅依赖标准公理 propext、Classical.choice、Quot.sound）。

新增两个文件，并已在 `RequestProject/Reduced.lean` 中引入；`FORMALIZATION.md` 也相应更新（`ARISTOTLE_SUMMARY.md` 未改动）。

## 1. 临界指数为正 α(p_c) > 0（`RequestProject/Reduced/Positivity.lean`）
基于已有的退火指数存在性（`Capstone.lean` 的 `reduced_annealed_exponent`），按论文论证给出均值的几何增长：
- `Dmean_ge_two_thirds`：在 p_diamond ≤ 1/2 区段，E[D_n] ≥ (2/3)E[R_n]（由 `Dmean_lower` 与相对二阶矩界 E[R_n²] ≤ 2E[R_n]²）；
- `E1_succ_ge`：结合一步递归得 E[R_{n+1}] ≥ (2 − (4/3)p_diamond)·E[R_n]；
- `E1_ge_geom`：迭代得 E[R_n] ≥ (2 − (4/3)p_diamond)^n；
- `annealed_exponent_ge_log`：故 α ≥ log(2 − (4/3)p_diamond)；
- 主定理 `alpha_pc_pos`：在 p_c 处（p_diamond = √5 − 2）增长因子为 (14 − 4√5)/3 > 1，于是 α(p_c) ≥ log((14 − 4√5)/3) > 0，即 α(p_c) > 0。

## 2. 不存在确定性极限（`RequestProject/Reduced/NoLimit.lean`）
主定理 `no_deterministic_limit`：设 p_series, p_diamond ∈ (0,1)，λ > 0，Z_n = λ^n R_n；若 Z_n 依分布收敛到确定常数 c ≥ 0，则 c = 0。"依分布收敛到 c" 用其特征性质刻画——对每个有界连续 f，∫ f dν_n → f(c)。证明完全在分布递归层面进行：
- `zMeasure_succ_integral`：Z_n 的律的一步递归（∫ f dν_{n+1} = p_series·∫f(λ(a+b)) d(ν_n⊗ν_n) + p_diamond·∫f(λ·diamond) d(ν_n^⊗4)），由换元 `integral_map` 与并联齐次性 `par_smul` 搭起；
- `series_limit`：串联项 → f(2λc)（二重积上的连续映射定理）；
- `diamond_limit`：菱形项 → f(λc)；因并联映射在原点奇异，用全局连续截断 `diamondSafe` 比较真积分，用一个其质量随弱收敛趋于 0 的 bump 函数（`exists_bump4`）控制误差（c > 0 是关键）；
- `limit_identity`：结合极限唯一性得 ∀ f，f(c) = p_series·f(2λc) + p_diamond·f(λc)；
- 取一个在 c 取 1、在 2λc 与 λc 中与 c 不同的那个点取 0 的帐篷函数（`exists_tent`，结合 `exists_ne_of_pos`，因 c > 0 时 2λc ≠ λc），与 p_series, p_diamond > 0 矛盾，除非 c = 0。

弱收敛层基于 Mathlib 的 `ProbabilityMeasure` 弱拓扑（`tendsto_iff_forall_integral_tendsto`、`continuous_prod`）。其中假设 hlam : 0 < lam 按论文陈述保留（已在 docstring 注明实际证明未用到它）。

# Summary of changes for run 92b9054f-f5f5-42f3-9b4c-e4c00acacff4
是的，之前确实缺了这一部分——“把整列 R_n 实现在单一概率空间上”的构造此前未形式化（旧的 FORMALIZATION.md 里也明确把它列为未完成项）。本次我补上了它。

新增文件 `RequestProject/Reduced/JointSpace.lean`（已在 `RequestProject/Reduced.lean` 中引入），完整实现你描述的构造：

- 样本空间 `Ω := ℝ^ℕ`（`SamplePath`）；
- 联合律 `P := ⨂ₙ μ_n`（`jointMeasure`），用 Mathlib 的 `Measure.infinitePi` 取各层边际律 `μ_n = lawMeasure pd ps n` 的无穷乘积；
- `R_n := π_n` 取第 n 个坐标投影（`proj`）。

关键结果：
- `isProb_jointMeasure`：`P` 是概率测度；
- `jointMeasure_map_proj`：**边际恒等式** `(R_n)_* P = μ_n`（即投影 π_n 在 P 下的前推恰为第 n 层边际律）；
- 由此把已建立的边际事实——`1 ≤ R_n ≤ 2^n`、乘积矩界 `E[R_n]·E[1/R_n] ≤ 11/5`（`E1Einv_le`）、次可乘性 `E[R_{a+b}] ≤ E[R_a]·E[R_b]`（`E1_submultiplicative`）——正好喂给抽象定理 `reduced_quenched_exponent` 的假设 `hge`、`hle`、`hM`、`hsub`；
- 主定理 `reduced_quenched_exponent_concrete`：在 `pd ≤ 1/2`（包含临界参数 p_c）区段，存在确定常数 `α ∈ [0, log 2]`，使得 **P-几乎必然 `(1/n) log R_n → α`**（n → ∞）。

技术说明：抽象定理要求处处成立的界 `1 ≤ R_n ω ≤ 2^n`，而坐标投影只在 P-几乎必然意义下落在 `[1,2^n]`。为此通过截断过程 `Rclamp n ω := max 1 (min (2^n) (ω n))` 过渡：它处处满足界、与 π_n 几乎必然相等且积分一致；把几乎必然收敛从 `Rclamp` 转回坐标投影后，结论对 π_n 逐字成立。

全工程编译通过，`JointSpace.lean` 无 `sorry`/`admit`/`axiom`/`@[implemented_by]`，主定理仅依赖标准公理 `propext`、`Classical.choice`、`Quot.sound`。`FORMALIZATION.md` 已相应更新（`ARISTOTLE_SUMMARY.md` 未改动）。

# Summary of changes for run a245d8a0-f869-4ceb-8953-8526c296066e
我把原文（arXiv:2603.13798）Lemma 4.5（`lem:uniform_product`，"统一乘积矩界" `E[R_n]·E[1/R_n] ≤ M(p)`）中此前只完成了 Case 1（`p_diamond ≤ 1/2`）的工作，补全为 **Case 2 与 Case 3**，从而该引理对所有 `p ∈ (0,1)` 都被机器验证。新增内容全部位于 `RequestProject/Reduced/Cases23.lean`（并在 `RequestProject/Reduced.lean` 中引入、在 `FORMALIZATION.md` 中记录）。全工程编译通过，无 `sorry`/`admit`/`axiom`/`@[implemented_by]`，主结果仅依赖标准公理 `propext`、`Classical.choice`、`Quot.sound`。

完成的核心定理：
- `uniform_product_case2`（Case 2，区间 `1/2 ≤ pd ≤ 1/√3`，形式化为 `1/2 ≤ pd ∧ pd² ≤ 1/3`）：仍得到 `E[R_n]·E[1/R_n] ≤ 11/5`。其关键是把相对二阶矩放宽到 `E[R²] ≤ 3·E[R]²`（`case2_inv` 的联立归纳），为此从零证明了四重乘积上的两条新 Cauchy–Schwarz 估计 `diamond_CS`（精化菱形二阶矩，给出 `E[D²] ≤ E[R]² − (5/3)(E[R]−E[D])²`）与 `harm_CS`（调和均值估计 `E[D] ≥ (5/11)E[R]`），以及三条新积分恒等式 `int_C_int`、`int_K_int`、`int_J_int`。
- `uniform_product_case3`（Case 3，`pd > 1/√3`，形式化为 `1/2 < pd ∧ pd < 1 ∧ 1/3 < pd²`）：给出有限统一界。相对二阶矩被 `(2−pd)/(2pd−1)` 控制（`E2_ratio_case3`），乘积矩满足收缩因子 `(3/2)(1−pd²) < 1` 的仿射递推（`affine_step`），迭代得有限界。
- `uniform_product_lemma45`：把 Case 1/2/3 合并，对任意 `0 < pd < 1`（并在 `pd > 1/√3` 区段附加单调性假设）统一给出有限的乘积矩界——即整条 Lemma 4.5。
- 配套引理：通用一步 logistic 估计 `logistic_step`、`coarse_E2`、基值 `E1_one`/`E2_one`、纯实数收尾不等式 `case2_close`/`case3_affine_close` 等。

关于 Case 3 的说明：原文 Case 3 用到电阻过程的几乎必然单调性 `R_{n+1} ≥ R_n`（图层面的 Rayleigh 单调性，来自耦合的迭代构造）。在本工程的"分布递归"模型里没有联合耦合，均值单调性也确实不是一步递归的推论，因此它作为显式假设 `hmono : ∀ k, E1 pd ps k ≤ E1 pd ps (k+1)` 出现——这正是原文从图构造中获得、再喂给 Case 3 的输入；Case 1、Case 2 不需要任何此类假设。这一点已在 `FORMALIZATION.md` 中如实记录。

# Summary of changes for run f5b892b8-c37b-4ee5-b603-fc8f37773a2d
## 回答：可以，凹性/Jensen 论证已被完整构造并机器验证

你问"证明需要对随机串并联网络做凹性/Jensen 论证这件事你可以自己构造吗"——可以。该论证已在 `RequestProject/Reduced/Submultiplicative.lean` 中完整构造，核心定理为 `E1_submultiplicative`：

  `E[R_{a+b}] ≤ E[R_a] · E[R_b]`（仅需参数约束 `0 ≤ pd`、`0 ≤ ps`、`ps+pd=1`，无额外假设）。

它把图的自相似复合论证整体搬到分布递归层面（无需 Mathlib 中缺失的有效电阻图论），关键构件包括：
- 带任意叶测度的广义律 `genLaw ν n` 及其复合恒等式 `genLaw ν (a+b) = genLaw (genLaw ν b) a`（"把底部 b 层网络替换为 R_b 叶子"）；
- 增-凹序 `IcvLEon`，并证明它被一步算子保持（`combineM_icv`、`genLaw_icv`）——这正是"串并联网络的有效电阻是叶电阻的增-凹函数"这一事实；
- Jensen（把叶律替换为其均值的点测度只增大均值，`jensen_le_dirac`）与齐次性（按比例缩放叶律即缩放均值，`mean_genLaw_dirac`）。

我本次的工作：核验了该论证确实成立（无 sorry、仅依赖 `propext`/`Classical.choice`/`Quot.sound`、全工程编译通过），并新增 `RequestProject/Reduced/Capstone.lean`，把它真正用起来以**去掉假设**：
- `E1_le_pow`：`E[R_n] ≤ 2^n`（确定性串联界）；
- `reduced_annealed_exponent`：把 `1 ≤ E[R_n] ≤ 2^n` 与 `E1_submultiplicative` 一起喂给 Fekete 引理，**无条件地**给出退火指数的存在性——存在确定常数 `α ∈ [0, log 2]` 使 `(log E[R_n])/n → α`。即原先作为输入的"均值次可乘性"现在是一条被证明的定理，退火指数对所建模型不再依赖任何额外假设。

## 关于抽象总成定理 `reduced_quenched_exponent` 中残留的 `hsub`
该总成定理是针对任意概率空间上任意过程 `R` 陈述的，因此把次可乘性写成形式假设 `hsub`；对具体模型而言，这个假设正由 `E1_submultiplicative` 提供（已由 `reduced_annealed_exponent` 无条件见证）。唯一未形式化的是：构造一个承载整列 `R_n`（给定边际律）的单一联合概率空间，这是把几乎必然的"淬火"收敛也对具体模型脱去抽象所需要的，属于另一独立的测度论构造。

`FORMALIZATION.md` 已相应更新（`ARISTOTLE_SUMMARY.md` 未改动）。全工程构建成功，无 `sorry`/`admit`/`axiom`/`@[implemented_by]`。

# Summary of changes for run 591a8ae1-faa9-464f-99f3-0735c1762842
## 目标
你要求把证明的两个核心结构性事实——"一致乘积矩界 M"与"均值的次可乘性"——从假设变成被验证的定理。

## 已完成：一致乘积矩界 M 已被完整验证（不再是假设）

我在 `RequestProject/Reduced/Moments.lean` 中，**直接从约化电阻过程的分布递归**（`lawMeasure`）出发，完整证明了一致乘积矩界，无 sorry、无新增公理（仅依赖 `propext`、`Classical.choice`、`Quot.sound`），整个项目编译通过。

核心定理（在 `pdiamond ≤ 1/2` 的区间内，该区间包含临界参数 `p_c`，此处 `pdiamond = √5 − 2 < 1/2`）：
- `E1Einv_le` / `uniform_product`：对所有 `n`，`E[R_n]·E[1/R_n] ≤ 11/5`。

为此我从零搭建并证明了所需的全部引理，包括：
- 矩的一步递归 `E1_succ`、`Einv_succ`、`E2_succ`，及其所需的乘积测度积分工具（Fubini/独立性、`prodAssoc` 重组、`int_prod_sum`、`int_prod4_ab` 等）；
- 钻石/并联估计 `Dmean_le_E1`、`Dsq_le_E1sq`、`Dmean_lower`，恒等式 `Sinv_eq`、`Wmean_eq`、`WSmean_eq`，以及一个可复用的积分 Cauchy–Schwarz 不等式 `integral_cauchy_schwarz_sq`；
- 相对二阶矩界 `E2_le_two_E1sq`（`E[R²] ≤ 2·E[R]²`）；
- 二者经一个 logistic 型一步收缩的耦合归纳，给出常数 `M = 11/5`。

也就是说，论文里作为输入的"乘积矩界 M"现在是一条被机器验证的定理，而非假设。

## 未完成：均值次可乘性仍为假设（并已说明原因）
`E[R_{a+b}] ≤ E[R_a]·E[R_b]` 在 `Limit.lean` 的总成定理 `reduced_quenched_exponent` 中仍以假设 `hsub` 出现。与乘积矩界不同，它**不能**仅由一步分布递归推出：它本质上表达图的自相似复合（`R_{n+m}` 等同于"把第 n 层网络的每条边换成独立的 R_m"），其证明需要对随机串并联网络做凹性/Jensen 论证，即 Mathlib 中没有、且属于本项目既定范围之外的有效电阻结构。我已数值核验它成立，但在本次会话中无法把这套基础设施完整建起来，故保留为假设，并在 `FORMALIZATION.md` 中如实记录了它的地位与所需路径。

## 文件
- 主要新增/完成：`RequestProject/Reduced/Moments.lean`（乘积矩界的完整证明）；`RequestProject/Reduced/RealAux.lean` 增加了 `par_le_quarter`。
- `FORMALIZATION.md` 已更新，说明乘积矩界 M 已被验证、次可乘性仍为假设及原因。
- 全工程 `grep` 无 `sorry`/`admit`/`axiom`/`@[implemented_by]`，构建成功。

# Summary of changes for run a2171eba-4e59-416c-bad1-16b998b09450
我阅读了 arXiv:2603.13798（*Iterated Graph Systems (I): random walks and diffusion limits*）的第 4.1 小节 "Solution to the open problem in [hambly2010diffusion]"，并将其核心分析内容形式化为一个无 sorry、仅依赖标准公理（propext、Classical.choice、Quot.sound）的 Lean 项目。整个项目可成功编译。

## 是否可以形式化？
可以。该小节研究钻石分层格上"约化二端电阻过程" (R_n)：从 R_0=1 出发，每步以概率 p_series 把每条边换成两条 i.i.d. 拷贝的串联 (X+Y)，以概率 p_diamond 换成四条拷贝的菱形 par(X₁+X₂, X₃+X₄)（par a b = ab/(a+b)）。按您选择的方案，我**直接通过分布递归来建模**，不重建 Mathlib 中没有的 EIGS / 随机图有效电阻理论。

## 形式化内容（位于 RequestProject/Reduced/）
- Params.lean：参数 pdiamond、pseries、pc 及其代数：pseries+pdiamond=1、正性、pc²=1−pc、pdiamond pc=√5−2、pdiamond pc<1/2。
- RealAux.lean：一步矩计算所需的初等实恒等式/不等式（菱形恒等式、倒数恒等式、par a b ≤ √(ab)/2、两个 logistic 型映射的单调性，以及推出 1≤R_n≤2ⁿ 的串/并确定性界）。
- Process.lean：把 R_n 的分布构造为测度序列 lawMeasure，证明每个 lawMeasure 都是概率测度（isProb_lawMeasure）且支撑在 [1,2ⁿ]（lawMeasure_support）。
- Limit.lean：分析核心。

## 主要定理
- fekete_exponent：指数 α 的存在性（"annealed exponent" 引理，由 Fekete 引理给出 α∈[0,log 2]）。
- quenched_ae：Theorem "reduced quenched exponent" 的几乎必然部分——由 Jensen 不等式、Markov 不等式与 Borel–Cantelli 引理证明，几乎必然有 (log R_n)/n → α。
- reduced_quenched_exponent（总成定理）：给定 1≤R_n≤2ⁿ、一致的乘积矩界 E[R_n]·E[1/R_n]≤M、以及均值的次可乘性（来自图的自相似性），则存在确定常数 α∈[0,log 2]，使得几乎必然 (log R_n)/n→α，且退火指数 (log E[R_n])/n→α 与 (E[log R_n])/n→α 都等于 α——即**淬火指数与退火指数相等**，这正是该开放问题的解答核心。

## 范围说明
- 图层面的约化命题（簇的有效电阻 =d R_n）超出范围，因为它需要 Mathlib 中没有的有效电阻/随机递归分形理论。
- 一致乘积矩界 M 与均值次可乘性作为总成定理的**显式假设**出现（它们正是 logistic_product / uniform_product 引理与（被略去的）图自相似性所提供的输入）。
- 显式的一步矩计算（logistic_product、uniform_product 求出常数 M）以及命题 α(p_c)>0 和"不存在确定性极限"尚未形式化，可作为后续工作。

项目根目录的 FORMALIZATION.md 给出了完整概览。所有结果均无 sorry、无新增公理。