import Solutions.J0RadialUniqueness.Verified
import Mathlib.Tactic

/-! Small explicit interfaces for the concise revised manuscript.
The original modules and their signed evidence are left unchanged. Every estimate
below concerns the actual factorial series, principal-branch kernels and radial
functions; no analytic premise is added to the final results. -/

noncomputable section
open Set
open scoped Topology

namespace J0RadialUniqueness

/-- A single compact-set majorant for the actual kernel and its complex derivative.
The statement also includes the empty compact set. -/
theorem revision_laplace_compact_control {L : Set ℂ} (hL : IsCompact L)
    (hsub : L ⊆ Complex.slitPlane) :
    ∃ m c C : ℝ, 0 < m ∧ 0 < c ∧ 0 < C ∧
      ∀ w ∈ L, ∀ t : ℝ, 0 ≤ t →
        m ≤ ‖w‖ ∧ c ≤ ‖laplaceBase w t‖ ∧ ‖laplaceKernel w t‖ ≤ C ∧
        HasDerivAt (fun v : ℂ => laplaceKernel v t)
          ((1 / (4 * w ^ 2)) * laplaceMomentKernel w t) w ∧
        ‖(1 / (4 * w ^ 2) : ℂ) * laplaceMomentKernel w t‖ ≤ C * t := by
  obtain ⟨m, c, hm, hc, hmb, hcb⟩ := laplace_compact_uniform_lower hL hsub
  let K : ℝ := Real.rpow c (-1 / 2 : ℝ)
  let B : ℝ := (1 / (4 * m ^ 2)) * Real.rpow c (-3 / 2 : ℝ)
  let C : ℝ := 1 + K + B
  have hK : 0 < K := Real.rpow_pos_of_pos hc _
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hKC : K ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  refine ⟨m, c, C, hm, hc, hC, ?_⟩
  intro w hw t ht
  have hb : c ≤ ‖laplaceBase w t‖ := hcb w hw t ht
  have hwpos : 0 < ‖w‖ := hm.trans_le (hmb w hw)
  have hinv : ‖(1 / (4 * w ^ 2) : ℂ)‖ ≤ (1 / (4 * m ^ 2) : ℝ) := by
    simp only [norm_div, norm_one, norm_mul, norm_pow, Complex.norm_ofNat]
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 4 * m ^ 2)
    nlinarith [hmb w hw]
  have hmoment := laplaceMomentKernel_norm_le_of_base_lower_bound ht hc hb
  refine ⟨hmb w hw, hb,
    (laplaceKernel_norm_le_of_base_lower_bound hc hb).trans hKC,
    laplaceKernel_hasDerivAt_moment (hsub hw) ht, ?_⟩
  calc
    ‖(1 / (4 * w ^ 2) : ℂ) * laplaceMomentKernel w t‖ =
        ‖(1 / (4 * w ^ 2) : ℂ)‖ * ‖laplaceMomentKernel w t‖ := norm_mul _ _
    _ ≤ (1 / (4 * m ^ 2)) * (t * Real.rpow c (-3 / 2 : ℝ)) :=
      mul_le_mul hinv hmoment (norm_nonneg _) (by positivity)
    _ = B * t := by dsimp [B]; ring
    _ ≤ C * t := mul_le_mul_of_nonneg_right hBC ht

/-- The shifted Abel identity and uniform strict contraction used for Q.
Only nonnegativity, monotonicity and summability of the actual coefficients are needed. -/
theorem revision_abel_contraction (b : ℕ → ℝ) (hb : Summable b)
    (hn : ∀ n, 0 ≤ b n) (hd : ∀ n, b (n + 1) ≤ b n) (h₀ : b 0 = 1)
    (u : ℂ) (hu : ‖u‖ < 1) :
    let d : ℕ → ℝ := fun n => b n - b (n + 1)
    (1 - u) * (∑' n : ℕ, (b n : ℂ) * u ^ n) =
        1 - ∑' n : ℕ, (d n : ℂ) * u ^ (n + 1) ∧
      ‖∑' n : ℕ, (d n : ℂ) * u ^ (n + 1)‖ ≤ ‖u‖ := by
  let d : ℕ → ℝ := fun n => b n - b (n + 1)
  change (1 - u) * (∑' n : ℕ, (b n : ℂ) * u ^ n) =
      1 - ∑' n : ℕ, (d n : ℂ) * u ^ (n + 1) ∧
    ‖∑' n : ℕ, (d n : ℂ) * u ^ (n + 1)‖ ≤ ‖u‖
  have hdpos : ∀ n, 0 ≤ d n := fun n => sub_nonneg.mpr (hd n)
  have hbshift : Summable (fun n => b (n + 1)) :=
    (summable_nat_add_iff 1).mpr hb
  have hds : Summable d := hb.sub hbshift
  have hdt : ∑' n, d n = 1 := by
    rw [show (∑' n, d n) = (∑' n, b n) - ∑' n, b (n + 1) from
      hb.tsum_sub hbshift]
    have he := hb.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at he
    linarith
  have hupow : ∀ n : ℕ, ‖u‖ ^ n ≤ 1 :=
    fun n => pow_le_one₀ (norm_nonneg _) hu.le
  have hs : Summable (fun n => (b n : ℂ) * u ^ n) := by
    apply hb.of_norm_bounded
    intro n
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hn n), norm_pow]
    exact mul_le_of_le_one_right (hn n) (hupow n)
  have hD : Summable (fun n => (d n : ℂ) * u ^ (n + 1)) := by
    apply hds.of_norm_bounded
    intro n
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hdpos n), norm_pow]
    exact mul_le_of_le_one_right (hdpos n) (hupow (n + 1))
  have ht : Summable (fun n => (b (n + 1) : ℂ) * u ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  have hmul : (∑' n, (d n : ℂ) * u ^ (n + 1)) =
      u * (∑' n, (b n : ℂ) * u ^ n) -
        ∑' n, (b (n + 1) : ℂ) * u ^ (n + 1) := by
    rw [← tsum_mul_left, ← (hs.mul_left u).tsum_sub ht]
    apply tsum_congr
    intro n
    simp only [d, Complex.ofReal_sub, pow_succ]
    ring
  have hbound : ‖∑' n, (d n : ℂ) * u ^ (n + 1)‖ ≤ ‖u‖ := by
    have hbnd : ∀ n, ‖(d n : ℂ) * u ^ (n + 1)‖ ≤ d n * ‖u‖ := by
      intro n
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hdpos n), norm_pow, pow_succ]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg _) (hupow n)) (hdpos n)
    have hh := hD.hasSum.norm_le_of_bounded (hds.mul_right ‖u‖).hasSum hbnd
    simpa [hds.tsum_mul_right, hdt] using hh
  refine ⟨?_, hbound⟩
  have he := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, pow_zero, mul_one, h₀, Complex.ofReal_one] at he
  linear_combination hmul - he

/-- Weak square-root and cosh estimates suffice at the closed radius boundary rho = 4. -/
theorem revision_one_point_cosh_bounds {z : ℂ} (hJ : J0 z = 1)
    (hz : PrincipalSector z) :
    Real.sqrt (8 * Real.pi) ≤ Real.sqrt (2 * Real.pi * ‖z‖) ∧
      Real.sqrt (2 * Real.pi * ‖z‖) ≤ (17 / 8 : ℝ) * Real.cosh z.im ∧
      (8 / 17 : ℝ) * Real.sqrt (8 * Real.pi) ≤ Real.cosh z.im ∧
      (11 / 5 : ℝ) < Real.cosh z.im := by
  have hr := one_point_norm_ge_four z (principalSector_ne_zero hz) hJ
  have hs := one_point_sqrt_bound_of_exact exact_decomposition hJ hz
  have hlow : Real.sqrt (8 * Real.pi) ≤ Real.sqrt (2 * Real.pi * ‖z‖) :=
    Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  have hhigh : Real.sqrt (2 * Real.pi * ‖z‖) ≤ (17 / 8 : ℝ) * Real.cosh z.im := by
    rw [Real.cosh_eq]
    linarith
  have hcosh : (8 / 17 : ℝ) * Real.sqrt (8 * Real.pi) ≤ Real.cosh z.im := by
    linarith
  exact ⟨hlow, hhigh, hcosh,
    lt_of_lt_of_le weighted_sqrt_eight_pi_gt_eleven_fifths hcosh⟩

/-- The initial height and exponential separation, without using Proposition 4.2 as input. -/
theorem revision_one_point_height_exp {z : ℂ} (hJ : J0 z = 1)
    (hz : PrincipalSector z) :
    (7 / 5 : ℝ) < z.im ∧ Real.exp (-2 * z.im) < (1 / 16 : ℝ) := by
  have hcosh := (revision_one_point_cosh_bounds hJ hz).2.2.2
  have hy : (7 / 5 : ℝ) < z.im := by
    by_contra hn
    have hm := Real.cosh_strictMonoOn.monotoneOn hz.1.le
      (by norm_num : (0 : ℝ) ≤ 7 / 5) (le_of_not_gt hn)
    linarith [cosh_seven_fifths_lt_eleven_fifths]
  refine ⟨hy, ?_⟩
  have h16 : (16 : ℝ) < Real.exp (2 * z.im) :=
    exp_fourteen_fifths_gt_sixteen.trans (Real.exp_lt_exp.mpr (by linarith))
  rw [show -2 * z.im = -(2 * z.im) by ring, Real.exp_neg]
  exact (inv_lt_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by norm_num; exact h16)

/-- The direct decaying square-root estimate used in the revised separation proof. -/
theorem revision_one_point_sqrt_decay {z : ℂ} (hJ : J0 z = 1)
    (hz : PrincipalSector z) :
    Real.sqrt (2 * Real.pi * ‖z‖) * Real.exp (-z.im) ≤ (17 / 16 : ℝ) ^ 2 := by
  have hs := one_point_sqrt_bound_of_exact exact_decomposition hJ hz
  have he := (revision_one_point_height_exp hJ hz).2
  have hh := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-z.im)).le
  have heq : (Real.exp z.im + Real.exp (-z.im)) * Real.exp (-z.im) =
      1 + Real.exp (-2 * z.im) := by
    rw [add_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> ring_nf <;> simp
  calc
    _ ≤ (17 / 16) * ((Real.exp z.im + Real.exp (-z.im)) * Real.exp (-z.im)) := by
      simpa only [mul_assoc] using hh
    _ = (17 / 16) * (1 + Real.exp (-2 * z.im)) := by rw [heq]
    _ ≤ (17 / 16 : ℝ) ^ 2 := by nlinarith

/-- The exact weak mass bound and both strict numerical comparisons from the revised text. -/
theorem revision_one_point_mass_chain {z : ℂ} (hJ : J0 z = 1)
    (hz : PrincipalSector z) :
    ‖z‖ * Real.exp (-2 * z.im) ≤ (17 / 16 : ℝ) ^ 4 / (2 * Real.pi) ∧
      (17 / 16 : ℝ) ^ 4 / (2 * Real.pi) < (17 / 16 : ℝ) ^ 4 / 6 ∧
      (17 / 16 : ℝ) ^ 4 / 6 < (11 / 50 : ℝ) := by
  have hd := revision_one_point_sqrt_decay hJ hz
  have hsq := (sq_le_sq₀
    (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
    (by norm_num : (0 : ℝ) ≤ (17 / 16 : ℝ) ^ 2)).mpr hd
  have hpow : (Real.sqrt (2 * Real.pi * ‖z‖) * Real.exp (-z.im)) ^ 2 =
      2 * Real.pi * (‖z‖ * Real.exp (-2 * z.im)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), pow_two, ← Real.exp_add]
    rw [show -z.im + -z.im = -2 * z.im by ring]
    ring
  rw [hpow] at hsq
  refine ⟨?_, ?_, by norm_num⟩
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
    nlinarith
  · apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)
      (by norm_num : (0 : ℝ) < 6)).mpr
    nlinarith [Real.pi_gt_three]

/-- The actual radial derivative estimate, separated from its final growth consequence. -/
theorem revision_radial_log_derivative {z : ℂ} (hJ : J0 z = 1)
    (hp : PrincipalSector z) (τ : ℝ) (hτ : 1 ≤ τ) :
    DifferentiableAt ℝ (rayLogNorm z) τ ∧ (7 / 25 : ℝ) < rayLogDerivative z τ := by
  have hy := (quantitative_separation z hJ hp).2.1
  let w : ℂ := (τ : ℂ) * z
  have hτpos : 0 < τ := by linarith
  have hwim : w.im = τ * z.im := by simp [w]
  have hwre : w.re = τ * z.re := by simp [w]
  have hclosed : ClosedPrincipalSector w := by
    have hzre : 0 < z.re := lt_trans hp.1 hp.2
    refine ⟨?_, ?_, ?_⟩
    · rw [hwim]; positivity
    · rw [hwim, hwre]; exact mul_le_mul_of_nonneg_left hp.2.le hτpos.le
    · rw [hwre]; exact mul_pos hτpos hzre
  have hs := ray_separation z hJ hp τ hτ
  have hwfour : 4 ≤ ‖w‖ := by
    have hs₀ : 4 ≤ ‖z‖ := one_point_norm_ge_four z (principalSector_ne_zero hp) hJ
    have hw : ‖w‖ = τ * ‖z‖ := by simp [w, norm_mul, abs_of_pos hτpos]
    rw [hw]
    nlinarith [norm_nonneg z]
  have ham := amplitude_modulus_bounds w hclosed hwfour
  have he := complex_radial_error_bound w
    (w * deriv APlus w / APlus w) (w * deriv AMinus w / AMinus w)
    (delta w) (deriv delta w) ham.2.2.2.2.1 ham.2.2.2.2.2
    hs.2.1 hs.2.2.1 (delta_derivative w hs.1)
  have hd := radial_derivative_decomposition z hJ hp τ hτ
  have hyw : (7 / 5 : ℝ) < w.im := by
    rw [hwim]
    nlinarith [hp.1]
  refine ⟨hd.1, ?_⟩
  apply radial_derivative_lower_bound hyw _ hd.2
  have hreal := Complex.abs_re_le_norm
    (w * deriv AMinus w / AMinus w + w * deriv delta w / (1 + delta w))
  exact (abs_lt.mp (lt_of_le_of_lt hreal he)).1

/-- The modified logarithm is strictly increasing, using ordinary derivatives at tau = 1. -/
theorem revision_ray_corrected_log_strictMono {z : ℂ} (hJ : J0 z = 1)
    (hp : PrincipalSector z) :
    StrictMonoOn (fun τ : ℝ => rayLogNorm z τ - (7 / 25 : ℝ) * Real.log τ) (Ici 1) := by
  let H : ℝ → ℝ := fun τ => rayLogNorm z τ - (7 / 25 : ℝ) * Real.log τ
  have hHderiv (τ : ℝ) (hτ : 1 ≤ τ) :
      HasDerivAt H (deriv (rayLogNorm z) τ - (7 / 25 : ℝ) * τ⁻¹) τ := by
    have hτpos : 0 < τ := by linarith
    exact (revision_radial_log_derivative hJ hp τ hτ).1.hasDerivAt.sub
      ((Real.hasDerivAt_log hτpos.ne').const_mul (7 / 25 : ℝ))
  have hpos (τ : ℝ) (hτ : 1 ≤ τ) :
      0 < deriv (rayLogNorm z) τ - (7 / 25 : ℝ) * τ⁻¹ := by
    have hτpos : 0 < τ := by linarith
    have hb := (revision_radial_log_derivative hJ hp τ hτ).2
    change (7 / 25 : ℝ) < τ * deriv (rayLogNorm z) τ at hb
    have hdiv : (7 / 25 : ℝ) / τ < deriv (rayLogNorm z) τ :=
      (div_lt_iff₀ hτpos).mpr (by simpa only [mul_comm] using hb)
    simpa only [div_eq_mul_inv] using sub_pos.mpr hdiv
  change StrictMonoOn H (Ici 1)
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
  · intro τ hτ
    exact (hHderiv τ hτ).continuousAt.continuousWithinAt
  · intro τ hτ
    have hτ' : 1 ≤ τ := interior_subset hτ
    rw [(hHderiv τ hτ').deriv]
    exact hpos τ hτ'

/-- The corrected logarithm starts at zero for an actual one-point. -/
theorem revision_ray_corrected_log_one {z : ℂ} (hJ : J0 z = 1) :
    rayLogNorm z 1 - (7 / 25 : ℝ) * Real.log 1 = 0 := by
  simp [rayLogNorm, hJ]

theorem revision_principal_sector_arg_iff (z : ℂ) :
    PrincipalSector z ↔ 0 < z.arg ∧ z.arg < Real.pi / 4 := by
  constructor
  · intro hz
    have hre : 0 < z.re := lt_trans hz.1 hz.2
    have hnonneg : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hz.1.le
    have hpos : 0 < z.arg := by
      apply lt_of_le_of_ne hnonneg
      intro he
      have hzero := (Complex.arg_eq_zero_iff.mp he.symm).2
      linarith [hz.1]
    have hhalf := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    have hm : z.arg ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], hhalf⟩
    have hq : Real.pi / 4 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have ht : Real.tan z.arg < Real.tan (Real.pi / 4) := by
      rw [Complex.tan_arg, Real.tan_pi_div_four]
      exact (div_lt_one hre).mpr hz.2
    exact ⟨hpos, (Real.strictMonoOn_tan.lt_iff_lt hm hq).mp ht⟩
  · intro hz
    have hz0 : z ≠ 0 := by intro he; simp [he, ClosedPrincipalSector] at hz
    have hn := norm_pos_iff.mpr hz0
    have hm : z.arg ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [hz.1,hz.2,Real.pi_pos]
    have hc := Real.cos_pos_of_mem_Ioo hm
    have hr : 0 < z.re := by
      rw [← Complex.norm_mul_cos_arg z]
      exact mul_pos hn hc
    have hi : 0 < z.im := by
      rw [← Complex.norm_mul_sin_arg z]
      exact mul_pos hn (Real.sin_pos_of_pos_of_lt_pi hz.1 (by linarith [hz.2,Real.pi_pos]))
    have hq : Real.pi / 4 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have ht := Real.strictMonoOn_tan hm hq hz.2
    rw [Complex.tan_arg,Real.tan_pi_div_four] at ht
    exact ⟨hi,(div_lt_one hr).mp ht⟩

theorem revision_closed_sector_arg_iff (z : ℂ) :
    ClosedPrincipalSector z ↔ z ≠ 0 ∧ 0 ≤ z.arg ∧ z.arg ≤ Real.pi / 4 := by
  constructor
  · intro hz
    have hz0 : z ≠ 0 := by intro he; simp [he, ClosedPrincipalSector] at hz
    have hhalf := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz.2.2)
    have hnonneg : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hz.1
    have hm : z.arg ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos],hhalf⟩
    have hq : Real.pi / 4 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have ht : Real.tan z.arg ≤ Real.tan (Real.pi / 4) := by
      rw [Complex.tan_arg,Real.tan_pi_div_four]
      exact (div_le_one hz.2.2).mpr hz.2.1
    exact ⟨hz0,hnonneg,(Real.strictMonoOn_tan.le_iff_le hm hq).mp ht⟩
  · rintro ⟨hz0,hlo,hhi⟩
    have hn := norm_pos_iff.mpr hz0
    have hm : z.arg ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have hr : 0 < z.re := by
      rw [← Complex.norm_mul_cos_arg z]
      exact mul_pos hn (Real.cos_pos_of_mem_Ioo hm)
    have hi : 0 ≤ z.im := Complex.arg_nonneg_iff.mp hlo
    have hq : Real.pi / 4 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_pos]
    have ht := Real.strictMonoOn_tan.monotoneOn hm hq hhi
    rw [Complex.tan_arg,Real.tan_pi_div_four] at ht
    exact ⟨hi,(div_le_one hr).mp ht,hr⟩

theorem revision_angle_ray_subsingleton (θ : ℝ) :
    Set.Subsingleton {r : ℝ | 0 < r ∧ J0 ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) = 1} := by
  intro a ha b hb
  exact paper_5_3 _ (Complex.exp_ne_zero _) a b ha.1 hb.1 ha.2 hb.2


end J0RadialUniqueness
