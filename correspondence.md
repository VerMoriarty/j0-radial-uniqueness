# Paper–Lean correspondence

Release 1.0.0. All 120 mathematical inventory items are covered, including the 16 numbered conclusions and Introduction A/B/C. Remark 6.6 is checked separately. Source line numbers identify the manuscript used for the mathematical correspondence review; the final citation-only edits preserve all mathematical environments byte for byte (see PUBLICATION.json).

The concise manuscript uses energy, shifted Abel contraction, genuine µ/tµ domination, segment mean-value estimates, weak intermediate cosh bounds, and corrected-log monotonicity. Full definitions, quantified types, exact local proof evidence, and dependency references for every item are in `correspondence.json`; private/generated dependencies are included in `dependency_closures.json`.

|Paper item|Source lines|Actual Lean entry|Relation|
|---|---|---|---|
|INTRO-A|83–90|`paper_5_2`|原样一致|
|INTRO-B|94–101|`revision_angle_ray_subsingleton`, `paper_5_3`|增强涵盖|
|INTRO-C|123–130|`paper_6_4`, `paper_6_5`, `paper_distribution_laplacian_bridge`|等价|
|N2.1|174–176|`F_rightHalfPlane`|原样一致|
|N2.2|191–193|`noRealOnePoints`|原样一致|
|N2.3|207–209|`Q_zero_free`, `Q_ne_zero_of_norm_lt_four`|原样一致|
|N2.4|229–233|`globalLocalization`|等价|
|N3.1|269–276|`paper_3_1`, `paper_laplace_integrability`|原样一致|
|N3.2|327–339|`paper_3_2`, `amplitude_integrability`, `exact_decomposition`|原样一致|
|N4.1|391–404|`paper_4_1`, `amplitude_derivatives`, `revision_closed_sector_arg_iff`|等价|
|N4.2|451–459|`paper_4_2`, `revision_principal_sector_arg_iff`, `quantitative_separation`|等价|
|N5.1|501–514|`paper_5_1`, `revision_radial_log_derivative`, `revision_principal_sector_arg_iff`|等价|
|N5.2|586–591|`paper_5_2`|原样一致|
|N5.3|603–608|`paper_5_3`, `revision_angle_ray_subsingleton`|增强涵盖|
|N6.1|640–649|`spectral_equivalence`|原样一致|
|N6.2|661–665|`paper_6_2`, `spectral_equivalence`|等价|
|N6.3|689–700|`paper_6_3`, `paper_distribution_laplacian_bridge`|等价|
|N6.4|702–711|`paper_6_4`, `paper_distribution_laplacian_bridge`|等价|
|N6.5|719–729|`paper_6_5`, `paper_distribution_laplacian_bridge`|等价|
|R6.6-BOUNDARY|739–744|`paper_boundary_finite_smooth_counterexample`, `paper_distribution_laplacian_bridge`|等价|
|R6.6-SUBCRITICAL|744–746|`paper_subcritical_smooth_counterexample`, `paper_distribution_laplacian_bridge`|等价|

## All retained proof steps

|Item|Lines|Meaning|Lean evidence|
|---|---|---|---|
|CTX-ABSTRACT-ESCAPE|54–58|摘要中的径向逃逸与射线唯一性|`paper_5_2`, `paper_5_3`|
|CTX-ABSTRACT-APPLICATION|62–65|摘要中的两半径应用|`paper_6_4`, `paper_6_5`, `not_mem_ratioSet_of_pos_ne_one`, `paper_5_3`, `paper_distribution_laplacian_bridge`|
|INTRO-A-IMPLICATION|92–92|径向逃逸排除第二个1点|`rayUniqueness_of_radialEscape`, `paper_5_2`|
|INTRO-SPECTRUM|108–115|二维公共谱方程及正比缩放改写|`spectral_equivalence`, `rayUniqueness_of_radialEscape`, `paper_5_2`|
|DEF-INTRO-BALL|124–124|引言中的开圆盘|`Plane`, `planeBall`|
|DEF-J0|156–160|J0的整函数幂级数|`J0`, `J0_series`, `fTerm_summable`|
|DEF-F|161–166|辅助整函数F|`F`, `fTerm`, `fTerm_summable`, `F_analyticOnNhd`|
|DEF-Q|161–166|辅助整函数Q|`Q`, `qTerm_summable`|
|SUP-J0-FQ|167–172|J0与F、Q的代数关系|`J0`, `F_sub_one`|
|P2.1-ODE|179–179|F的微分方程|`F_ode`, `F_firstDerivative_hasSum`, `F_secondDerivative_hasSum`, `F_ode_statement`|
|D2.1-hY|179–180|能量证明中的射线限制与平方模|`FRay`, `FRayNormSq`, `FRayAccel`, `FRaySlope`|
|P2.1-ENERGY|180–185|径向微分方程与积分能量恒等式|`FRay_ode`, `FRayFlux_hasDerivAt`, `FRayFlux_eq`, `FRayFlux_zero`, `FRay_energy`, `F_ode_statement`, `FRayNormSq_deriv`, `FRayNormSq_hasDerivAt`|
|P2.1-STRICT|186–188|能量正性与严格径向增长|`FRaySlope_exists_nonzero`, `FRay_energy_integral_pos`, `FRayNormSq_deriv_pos_of_ode`, `FRayNormSq_strictMonoOn_of_ode`, `F_ode_statement`, `F_rightHalfPlane`, `fRightHalfPlane_of_ode`|
|D2.2-qh|196–197|实轴能量证明中的q与h|`FRay`, `noRealOnePoints`|
|P2.2-ODE|196–197|负实射线上的微分方程|`FRay_ode`, `F_ode_statement`, `negativeAxisEnergy_hasDerivAt`|
|D2.2-E|198–200|耗散能量E|`negativeAxisEnergy`, `FRay_hasDerivAt`, `FRay_deriv`|
|P2.2-DISSIPATION|201–204|能量导数、严格耗散与实轴结论|`negativeAxisEnergy_hasDerivAt`, `negativeAxisEnergy_zero`, `negativeAxisEnergy_one_lt_one`, `F_negative_real_norm_lt_one`, `noRealOnePoints`|
|D2.3-COEFF|212–215|Abel变换中的u、b_n及d_n|`qScaledCoeff`, `Q_ne_zero_of_norm_lt_four`, `revision_abel_contraction`|
|P2.3-COEFF|212–215|系数正性、可和性及单调性|`qScaledCoeff_summable`, `qScaledCoeff_decreasing`, `Q_ne_zero_of_norm_lt_four`, `qScaledCoeff`|
|P2.3-ABEL|215–220|Abel变换与望远镜求和|`revision_abel_contraction`, `decreasing_series_ne_zero`, `qScaledCoeff_summable`, `qScaledCoeff_decreasing`, `Q_ne_zero_of_norm_lt_four`|
|P2.3-NONZERO|221–226|尾和模小于1推出无零点|`revision_abel_contraction`, `decreasing_series_ne_zero`, `Q_ne_zero_of_norm_lt_four`, `qScaledCoeff_summable`, `qScaledCoeff_decreasing`|
|D2.4-w|236–236|定位证明的变量w|`globalLocalization`, `J0`|
|P2.4-HALFPLANE|236–238|排除Re(z²)≤0|`globalLocalization`, `F_rightHalfPlane`|
|P2.4-REAL|238–239|排除实1点|`globalLocalization`, `noRealOnePoints`|
|P2.4-RADIUS|239–240|无零圆盘推出模至少4|`one_point_norm_ge_four`, `F_sub_one`, `Q_ne_zero_of_norm_lt_four`|
|CTX-FOUR-SECTORS|243–245|四个开扇区与对称化|`globalLocalization`, `quadrantRep_orbit`, `quadrantRep_in_principalSector`, `J0_quadrantRep`, `revision_principal_sector_arg_iff`|
|DEF-OMEGA|249–249|切割平面Ω|`laplaceKernel`, `K0Series_analyticOnNhd`|
|DEF-LOG-POWERS|249–251|主值对数及半整数幂|`laplaceKernel`, `K0Series`, `log_pi_div_two_mul`|
|DEF-K0|251–252|K0的分支选择|`K0Series`, `K0_series_convergence`, `K0Series_analyticOnNhd`|
|DEF-MU|253–256|Laplace积分中的测度μ|`muDensity`, `weightedIntegral`, `muDensity_integrableOn`|
|SUP-MU-MOMENTS|257–260|μ的质量和一阶矩|`mu_moments`, `muDensity_integrableOn`, `firstMoment_integrableOn`, `muDensity_integral`, `firstMoment_integral`, `firstMoment_density_eq`|
|DEF-I|261–265|Laplace振幅I|`laplaceI`, `laplaceKernel`, `weightedIntegral`, `laplace_weighted_kernel_integrable`, `laplaceMomentKernel`|
|DEF-KCAL|265–267|Laplace函数Kcal|`laplaceK`|
|P3.1-CUT|279–282|积分核避开主值切割|`laplaceBase_mem_slitPlane`, `laplaceBase_ne_zero`, `laplaceKernel_hasDerivAt`|
|P3.1-COMPACT|284–291|紧集上的统一非退化界|`laplace_compactified_ne_zero`, `laplace_compact_uniform_lower`|
|P3.1-KERNEL-BOUND|291–303|紧集上的核与导数可积控制|`laplace_compact_uniform_lower`, `revision_laplace_compact_control`, `laplaceKernel_hasDerivAt_moment`, `laplaceKernel_norm_le_of_base_lower_bound`, `laplaceMomentKernel_norm_le_of_base_lower_bound`|
|P3.1-HOLOMORPHY|302–305|积分号下求导与全纯性|`laplaceI_hasDerivAt`, `laplaceI_differentiableOn`, `laplaceK_differentiableOn`, `muDensity_integrableOn`, `firstMoment_integrableOn`, `laplace_weighted_kernel_integrable`, `laplace_weighted_moment_integrable`, `muDensity_nonneg`, `laplaceK_differentiableAt`, `firstMoment_density_eq`|
|P3.1-K0-POSITIVE|307–310|正实轴上K0的标准积分表示|`paper_k0_cosh_integral`, `K0Series_ofReal_cosh_integral`, `complexCoshKernel_integrable`|
|P3.1-SUBSTITUTION|311–315|正实轴换元识别Kcal|`laplaceK_ofReal_kernel_integral`, `laplaceK_eq_K0Series_positive_real`, `realLaplaceKernel_affine`, `realLaplaceKernel_integral_eq_spectral`, `positiveSpectralKernel_integral_eq_cosh`, `positiveSpectralKernel_cosh_jacobian`, `positiveLaplaceWeight_eq_realLaplaceKernel`, `positiveLaplace_affine_hasDerivAt`, `positiveLaplace_affine_image`, `positiveLaplace_affine_injOn`, `positiveSpectralKernel_integrable`, `positiveCosh_image`, `positiveCosh_injOn`, `positiveCosh_sqrt_jacobian`, `realCoshKernel_integrable`|
|P3.1-IDENTITY-THEOREM|316–318|恒等定理延拓到Ω|`laplaceIdentification_of_positive_real`, `laplaceK_eq_K0Series_positive_real`, `K0Series_analyticOnNhd`, `k_laplace_identification`|
|DEF-HPLUS|321–321|右半平面H+|`rightHalfPlane`|
|DEF-APM|321–325|右半平面上的A_±|`APlus`, `AMinus`, `plusKernel`, `minusKernel`, `weightedIntegral`, `amplitude_integrability`, `minusMomentKernel`, `plusMomentKernel`|
|P3.2-CHAIN|342–345|A_±识别为I的旋转复合|`negI_mul_mem_slitPlane`, `I_mul_mem_slitPlane`, `APlus_eq_laplaceI`, `AMinus_eq_laplaceI`, `APlus_hasDerivAt`, `AMinus_hasDerivAt`, `rotated_moment_minus`, `rotated_moment_plus`|
|P3.2-LOG|347–352|旋转后的主值对数恒等式|`log_I_mul_rightHalf`, `log_negI_mul_rightHalf`|
|P3.2-POWERS|353–358|旋转后的主值负半次幂|`cpow_I_mul_neg_half`, `cpow_negI_mul_neg_half`|
|P3.2-K0-AMPLITUDES|359–365|K0(±iz)的精确振幅表达|`exactDecomposition_of_laplaceIdentification`, `k_laplace_identification`, `laplace_prefactor_plus_product`, `laplace_prefactor_minus_product`, `log_pi_div_two_mul`, `log_two_pi_mul`, `cpow_I_mul_neg_half`, `cpow_negI_mul_neg_half`, `exact_decomposition`|
|P3.2-CONNECTION|366–372|K0与J0的连接公式|`K0_connection`|
|P3.2-COEFFICIENTS|372–380|系数化简完成J0分解|`quarter_phase_plus`, `quarter_phase_minus`, `component_phase_plus`, `component_phase_minus`, `laplace_prefactor_plus_product`, `laplace_prefactor_minus_product`, `exactDecomposition_of_laplaceIdentification`, `k_laplace_identification`, `exact_decomposition`|
|DEF-SECTOR-KAPPA|388–389|闭主扇区参数与κ|`ClosedPrincipalSector`, `kappa`, `revision_closed_sector_arg_iff`|
|P4.1-GEOMETRY|407–413|积分核线段的几何模下界|`sector_plus_base_norm_sq`, `sector_minus_base_norm_sq`|
|P4.1-SEGMENT-CUT|414–418|线段避割与复幂的实参数导数界|`imaginary_kernel_im`, `amplitude_bases_mem_slitPlane`, `inverse_sqrt_sub_one_bound`, `plusKernel_sub_one_bound`, `minusKernel_sub_one_bound`|
|P4.1-KERNEL-MVT|418–422|线段积分的均值估计|`plusKernel_sub_one_bound`, `minusKernel_sub_one_bound`, `inverse_sqrt_sub_one_bound`|
|P4.1-INTEGRATE|423–425|积分矩给出A误差与导数界|`amplitude_uniform_estimates`, `amplitude_integrability`, `firstMoment_integral`, `firstMoment_integrableOn`, `weightedIntegral_norm_le_half`|
|P4.1-MODULUS|427–433|ρ≥4时振幅严格非零及对数导数小量|`amplitude_modulus_bounds`, `kappa_div_lt_one_sixteenth`, `norm_bounds_of_norm_sub_one_lt`, `logarithmic_amplitude_bound`, `amplitudeModulusBounds_of_uniform`|
|DEF-U|436–439|两个振幅均非零的开域U|`amplitudeDomain`|
|SUP-U-OPEN|440–440|U是开集|`amplitudeDomain_isOpen`|
|DEF-DELTA|441–444|增长与衰减分量之比δ|`delta`, `amplitudeDomain`|
|SUP-J0-FACTOR|445–449|含δ的J0因式分解|`paper_factorization`, `factorization_of_exactDecomposition`|
|P4.2-RADIUS-U|462–463|定位保证ρ≥4及U成员关系|`one_point_norm_ge_four`, `amplitude_modulus_bounds`, `quantitative_separation`, `quantitativeSeparation_of_exact`|
|P4.2-TRIANGLE|464–470|1点方程给出双曲余弦下界|`revision_one_point_cosh_bounds`, `one_point_sqrt_bound_of_exact`, `exact_decomposition`, `weighted_sqrt_eight_pi_gt_eleven_fifths`|
|P4.2-NUMERIC|470–472|显式常数比较给y与指数界|`revision_one_point_height_exp`, `cosh_seven_fifths_lt_eleven_fifths`, `exp_fourteen_fifths_gt_sixteen`|
|P4.2-DELTA|474–479|δ的绝对值小于17/240|`norm_delta`, `delta_lt_of_amplitudes`, `quantitative_separation`, `quantitativeSeparation_of_exact`|
|P4.2-DECAY-SQRT|480–485|带指数衰减的平方根估计|`revision_one_point_sqrt_decay`|
|P4.2-DECAY|486–492|ρexp(−2y)的显式上界|`revision_one_point_mass_chain`|
|D5.1-RAY|503–505|外向射线及其模、虚部|`raySeparation_of_initial_amplitudes_factorization`, `ray_separation`, `rayLogNorm`, `rayLogDerivative`|
|D5.1-RHO-Y|517–518|射线上的ρτ和yτ|`raySeparation_of_initial_amplitudes_factorization`, `ray_separation`|
|P5.1-SECTOR|518–520|振幅界沿整个射线适用|`principalSector_real_mul`, `raySeparation_of_initial_amplitudes_factorization`, `ray_separation`, `amplitude_modulus_bounds`|
|P5.1-DECAY-MONOTONE|522–529|径向缩放下的指数衰减因子不增|`outward_exponential_factor_le_one_of_separation`, `outward_rho_exp_bound`, `quantitative_separation`, `outward_exponential_factor_le_one`|
|P5.1-DECAY-PROPAGATE|529–533|传播ρτexp(−2yτ)及指数上界|`outward_rho_exp_eleven_fiftieths`, `outward_exp_bound`, `raySeparation_of_initial_amplitudes_factorization`, `ray_separation`|
|P5.1-DELTA-PROPAGATE|533–538|δ与ρδ的传播界|`ray_separation`, `raySeparation_of_initial_amplitudes_factorization`, `norm_delta`, `weighted_delta_lt_of_amplitudes`|
|P5.1-NONZERO|539–544|整条外向射线上J0无零|`ray_separation`, `raySeparation_of_initial_amplitudes_factorization`, `one_add_ne_zero_of_norm_lt`, `paper_factorization`|
|P5.1-DIFFERENTIABLE|546–548|径向log模的可微性|`radial_derivative_decomposition`, `radialDerivativeDecomposition_of_factorization_and_ray`, `hasDerivAt_log_norm`|
|P5.1-LOG-DERIVATIVE|549–558|径向对数导数精确分解|`radial_derivative_decomposition`, `radialDerivativeDecomposition_of_factorization_and_ray`|
|P5.1-DELTA-DERIVATIVE|559–565|δ的复导数恒等式|`delta_derivative`, `delta_derivative_of_hasDerivAt`, `deltaDerivative_of_amplitudeDerivative`|
|P5.1-ERROR|566–574|对数导数扰动项小于31/50|`complex_radial_error_bound`, `radial_error_bound`, `radial_error_constant`, `revision_radial_log_derivative`|
|P5.1-MARGIN|575–576|7/25的正径向余量|`revision_radial_log_derivative`, `radial_derivative_lower_bound`, `radial_margin_identity`|
|D5.1-H|577–580|扣除目标增长后的函数H|`rayLogNorm`, `revision_ray_corrected_log_strictMono`|
|P5.1-MVT|581–583|正导数与中值定理给逃逸|`revision_ray_corrected_log_strictMono`, `revision_ray_corrected_log_one`, `logarithmic_growth_seven_twentyfifths`, `principalRadialEscape_of_analytic_inputs`, `paper_5_1`, `logarithmic_growth_of_radial_derivative`|
|P5.2-SYMMETRY|594–595|J0的偶性和共轭对称|`J0_neg`, `J0_conj`, `F_conj`, `fTerm_conj`|
|D5.2-w|595–598|将任意1点映到主扇区的w|`quadrantRep`, `quadrantRep_orbit`, `quadrantRep_in_principalSector`, `globalLocalization`, `revision_principal_sector_arg_iff`|
|P5.2-REDUCTION|598–600|对称化保留1点与整条射线模|`J0_quadrantRep`, `norm_J0_mul_quadrantRep`, `radialEscape_of_principal`, `paper_5_2`, `quadrantRep_pos_mul`|
|P5.3-CONTRADICTION|610–615|两半径反证唯一性|`rayUniqueness_of_radialEscape`, `paper_5_2`, `paper_5_3`, `revision_angle_ray_subsingleton`|
|DEF-BALL|619–619|两半径章节的开圆盘|`Plane`, `planeBall`|
|DEF-CIRCULAR-MEAN|619–625|L1_loc函数的规范圆周均值|`circleDirection`, `circularMean`, `paper_circle_mean_well_defined`|
|SUP-CIRCULAR-WELLDEFINED|625–627|均值的局部可积与代表元独立性|`paper_circle_mean_well_defined`|
|DEF-Z|633–635|非零1点集合Z|`onePoints`|
|DEF-RATIO-SET|635–638|谱根比值集A|`ratioSet`, `onePoints`|
|P6.1-FORWARD|652–653|根比值构造共同谱参数|`spectral_equivalence`|
|P6.1-REVERSE|653–655|共同非零谱构造根比值|`spectral_equivalence`|
|D6.2-EXPONENTIAL|668–668|平面指数谱函数Fλ|`spectralExponential`|
|P6.2-MEAN-EIGENFUNCTION|668–673|指数函数的圆均值特征值|`spectralExponential_circle_factor`, `integral_exp_mul_cos_eq_J0`, `circularMean_spectralExponential`, `spectralExponential_circle_intervalIntegrable`|
|P6.2-FIXED-LAPLACIAN|674–677|两个均值固定但Laplacian非零|`circularMean_spectralExponential`, `laplacian_spectralExponential`, `spectralExponential_zero`, `exists_spectral_nonharmonic_witness`|
|P6.2-REAL-EXTRACTION|677–678|取实部或虚部得到实反例|`exists_spectral_nonharmonic_witness`, `circularMean_spectralRealPart_of_J0_eq_one`, `circularMean_spectralImagPart_of_J0_eq_one`, `paper_6_2`|
|SUP-POSITIVE-RATIO-REMOVAL|681–685|排除全部正非单位谱比值|`not_mem_ratioSet_of_pos_ne_one`, `paper_5_3`|
|P-POSITIVE-RATIO-REMOVAL|686–687|根比值排除的射线论证|`positive_ratio_eq_one_of_rayUniqueness`, `paper_5_3`, `rayUniqueness_of_radialEscape`, `paper_5_2`|
|P6.4-APPLICATION|713–717|自动谱排除后应用Volchkov定理|`localTwoRadius_of_rayUniqueness_and_volchkov`, `paper_5_3`, `paper_6_3`, `paper_6_4`|
|P6.5-EXHAUSTION|731–734|任意大圆盘限制与分布调和性|`meanIdentityOn_of_global`, `globalDistributionHarmonic_of_local`, `paper_6_4`, `paper_6_5`|
|P6.5-WEYL|734–735|Weyl引理给光滑调和代表元|`paper_weyl_regularization`, `global_weyl`|
|P6.5-CONTINUOUS|735–736|连续性及调和均值定理给最终结论|`continuous_harmonic_of_distribution`, `circularMean_eq_of_harmonicOnNhd`, `paper_all_radius_mean_value`|

Types may use Cartesian sectors, ambient representatives, or pairwise uniqueness instead of polar notation/cardinality. The corresponding equivalences, same-domain L¹loc hypotheses, and actual Laplacian are recorded item by item. Generic lemmas are instantiated with proved inputs. Local facts count only with an exact source span and the kernel-checked enclosing declaration.

Background attribution is not a Lean proposition; see `review/source_check.md`. The code availability claim is fulfilled by this fixed source archive. The numbered conjunction alone does not certify all unnumbered proof steps or geometric counterexamples.
