import Solutions.J0RadialUniqueness.HelmholtzResolventSectorBound
import Solutions.J0RadialUniqueness.PlanarHelmholtzResolvent
import Solutions.J0RadialUniqueness.NumericalBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A true principal-sector convolution bound for the actual compact B
resolvent. The full-scale sector estimate is integrated down to radius zero;
the only singular majorant is the integrable power `s^(-1/2)`. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Interval

namespace J0RadialUniqueness

def resolventEnvelopeUpper (s L : ℝ) : ℝ :=
  (2 / (Real.sqrt s * Real.sqrt L)) * (1 + kappa / s)

theorem rotatedK0Envelope_le_resolventEnvelopeUpper {lam : ℂ}
    (hL : (1 : ℝ) ≤ ‖lam‖) {s : ℝ} (hs : 0 < s) :
    rotatedK0Envelope ((s : ℂ) * lam) ≤ resolventEnvelopeUpper s ‖lam‖ := by
  have hLpos : 0 < ‖lam‖ := by linarith
  have hn : ‖(s : ℂ) * lam‖ = s * ‖lam‖ := by
    rw [norm_mul, Complex.norm_of_nonneg hs.le]
  have hquot : Real.pi / (2 * (s * ‖lam‖)) ≤ 4 / (s * ‖lam‖) := by
    have h := div_le_div_of_nonneg_right
      (show Real.pi / 2 ≤ (4 : ℝ) by linarith [Real.pi_lt_four])
      (mul_nonneg hs.le (norm_nonneg lam))
    simpa only [div_div] using h
  have hroot : Real.sqrt (Real.pi / (2 * (s * ‖lam‖))) ≤
      2 / (Real.sqrt s * Real.sqrt ‖lam‖) := by
    refine (Real.sqrt_le_sqrt hquot).trans_eq ?_
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_mul hs.le]
    norm_num
  have hden : s ≤ s * ‖lam‖ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hL hs.le
  have hfac : 1 + kappa / (s * ‖lam‖) ≤ 1 + kappa / s := by
    exact add_le_add (le_refl (1 : ℝ)) (div_le_div_of_nonneg_left kappa_pos.le hs hden)
  unfold rotatedK0Envelope resolventEnvelopeUpper
  rw [hn]
  have hk := kappa_pos.le
  exact mul_le_mul hroot hfac (by positivity) (by positivity)

theorem resolventEnvelopeUpper_product {r s L : ℝ} (hL : 0 ≤ L) :
    resolventEnvelopeUpper r L * resolventEnvelopeUpper s L =
      (4 / (L * Real.sqrt r * Real.sqrt s)) * (1 + kappa / r) * (1 + kappa / s) := by
  have hden : (Real.sqrt r * Real.sqrt L) * (Real.sqrt s * Real.sqrt L) =
      L * Real.sqrt r * Real.sqrt s := by
    calc
      _ = (Real.sqrt L * Real.sqrt L) * Real.sqrt r * Real.sqrt s := by ring
      _ = _ := by rw [Real.mul_self_sqrt hL]
  unfold resolventEnvelopeUpper
  calc
    _ = ((2 / (Real.sqrt r * Real.sqrt L)) * (2 / (Real.sqrt s * Real.sqrt L))) *
        (1 + kappa / r) * (1 + kappa / s) := by ring
    _ = _ := by rw [div_mul_div_comm, hden]; norm_num

/-- A coarser numerical constant avoids any large-argument restriction on the
inner radial scale. The spectral decay `1 / ‖lam‖` is retained exactly. -/
theorem helmholtzResolventB_weighted_principal_bound {lam : ℂ}
    (hlam : ClosedPrincipalSector lam) (hL : (1 : ℝ) ≤ ‖lam‖)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r) :
    (2 * Real.pi * s) * ‖helmholtzResolventB r lam s‖ ≤
      (32 * Real.exp (r * lam.im) / ‖lam‖ * (1 + kappa / r) / Real.sqrt r) *
        (Real.sqrt r + kappa * Real.rpow s (-1 / 2 : ℝ)) := by
  have hLpos : 0 < ‖lam‖ := by linarith
  have hEr := rotatedK0Envelope_nonneg (z := (r : ℂ) * lam)
  have hEs := rotatedK0Envelope_nonneg (z := (s : ℂ) * lam)
  have hsector := helmholtzResolventB_sector_bound hlam hr hs hsr
  have hexp : Real.exp ((r - s) * lam.im) ≤ Real.exp (r * lam.im) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hs.le hlam.1]
  have hsector' : (2 * Real.pi ^ 2) * ‖helmholtzResolventB r lam s‖ ≤
      2 * rotatedK0Envelope ((r : ℂ) * lam) * rotatedK0Envelope ((s : ℂ) * lam) *
        Real.exp (r * lam.im) :=
    hsector.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hπsq : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hc := mul_le_mul_of_nonneg_right hπsq (norm_nonneg (helmholtzResolventB r lam s))
  have hB : ‖helmholtzResolventB r lam s‖ ≤
      rotatedK0Envelope ((r : ℂ) * lam) * rotatedK0Envelope ((s : ℂ) * lam) *
        Real.exp (r * lam.im) := by nlinarith only [hc, hsector']
  have hUr : 0 ≤ resolventEnvelopeUpper r ‖lam‖ := by
    unfold resolventEnvelopeUpper
    have hk := kappa_pos.le
    positivity
  have hprod := mul_le_mul (rotatedK0Envelope_le_resolventEnvelopeUpper hL hr)
    (rotatedK0Envelope_le_resolventEnvelopeUpper hL hs) hEs hUr
  have hprod' := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (r * lam.im)).le
  have hsmall : (s / Real.sqrt s) * (1 + kappa / s) = Real.sqrt s + kappa / Real.sqrt s := by
    rw [mul_add, mul_one]
    have heq : (s / Real.sqrt s) * (kappa / s) = kappa / Real.sqrt s := by
      field_simp [hs.ne', (Real.sqrt_pos.mpr hs).ne']
    rw [heq, Real.div_sqrt]
  have hradical : (Real.sqrt s)⁻¹ = Real.rpow s (-1 / 2 : ℝ) := by
    rw [Real.rpow_eq_pow, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg hs.le, ← Real.sqrt_eq_rpow]
  have hDnonneg : 0 ≤ 32 * Real.exp (r * lam.im) / ‖lam‖ *
      (1 + kappa / r) / Real.sqrt r := by
    have hk := kappa_pos.le
    positivity
  calc
    _ ≤ (8 * s) * (rotatedK0Envelope ((r : ℂ) * lam) *
        rotatedK0Envelope ((s : ℂ) * lam) * Real.exp (r * lam.im)) := by
      apply mul_le_mul _ hB (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four] : 2 * Real.pi ≤ (8 : ℝ)) hs.le
    _ ≤ (8 * s) * (resolventEnvelopeUpper r ‖lam‖ *
        resolventEnvelopeUpper s ‖lam‖ * Real.exp (r * lam.im)) :=
      mul_le_mul_of_nonneg_left hprod' (by positivity)
    _ = (32 * Real.exp (r * lam.im) / ‖lam‖ * (1 + kappa / r) / Real.sqrt r) *
        ((s / Real.sqrt s) * (1 + kappa / s)) := by
      rw [resolventEnvelopeUpper_product (norm_nonneg lam)]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (32 * Real.exp (r * lam.im) / ‖lam‖ * (1 + kappa / r) / Real.sqrt r) *
        (Real.sqrt s + kappa * Real.rpow s (-1 / 2 : ℝ)) := by
      rw [hsmall]
      simp only [div_eq_mul_inv, hradical]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (Real.sqrt_le_sqrt hsr) (le_refl _)) hDnonneg

/-- The true circular mean is bounded by the supremum bound on the compact
translated ball. -/
theorem norm_circularMean_le_closedBall_bound {u : Plane → ℂ} (x : Plane)
    {r s M : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r)
    (hM : ∀ y ∈ Metric.closedBall x r, ‖u y‖ ≤ M) : ‖circularMean u s x‖ ≤ M := by
  have hi : ‖∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, u (x + s • circleDirection θ)‖ ≤
      M * (2 * Real.pi) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 2 * Real.pi)
      (f := fun θ : ℝ => u (x + s • circleDirection θ)) (C := M) (fun θ _ => by
        apply hM
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, norm_circleDirection, mul_one, abs_of_nonneg hs]
        exact hsr)
    simpa only [sub_zero, abs_of_pos Real.two_pi_pos] using h
  rw [circularMean, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr Real.two_pi_pos)]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (M * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr Real.two_pi_pos.le)
    _ = M := by rw [mul_left_comm, inv_mul_cancel₀ Real.two_pi_pos.ne', mul_one]

theorem integral_rpow_neg_half_zero_radius (r : ℝ) :
    (∫ s : ℝ in (0 : ℝ)..r, Real.rpow s (-1 / 2 : ℝ)) = 2 * Real.sqrt r := by
  have h := integral_rpow (a := (0 : ℝ)) (b := r) (r := (-1 / 2 : ℝ))
    (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))
  norm_num [Real.rpow_eq_pow] at h
  rw [← Real.sqrt_eq_rpow] at h
  simpa [Real.rpow_eq_pow, div_eq_mul_inv, mul_comm] using h

/-- Integration of the full-scale sector majorant. The constant is independent
of the spectral parameter, and the original planar integral is the actual
compact resolvent convolution. -/
theorem resolventB_principal_convolution_bound_of_closedBall_bound
    {u : Plane → ℂ} (hu : Continuous u) (x : Plane) {r M : ℝ}
    (hr : 0 < r) (hMpos : 0 < M)
    (hM : ∀ y ∈ Metric.closedBall x r, ‖u y‖ ≤ M)
    {lam : ℂ} (hlam : ClosedPrincipalSector lam) (hL : (1 : ℝ) ≤ ‖lam‖) :
    ‖∫ y : Plane, compactRadialComplexKernel r (helmholtzResolventB r lam) y * u (x - y)‖ ≤
      (32 * M * (1 + kappa / r) * (r + 2 * kappa)) *
        Real.exp (r * lam.im) / ‖lam‖ := by
  let D : ℝ := 32 * Real.exp (r * lam.im) / ‖lam‖ * (1 + kappa / r) / Real.sqrt r
  have hD : 0 ≤ D := by
    dsimp [D]
    have hk := kappa_pos.le
    positivity
  have hpow : IntervalIntegrable (fun s : ℝ => Real.rpow s (-1 / 2 : ℝ)) volume 0 r := by
    simpa only [Real.rpow_eq_pow] using
      (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := r)
        (r := (-1 / 2 : ℝ)) (by norm_num))
  have hq : IntervalIntegrable (fun s : ℝ => Real.sqrt r + kappa * Real.rpow s (-1 / 2 : ℝ))
      volume 0 r := intervalIntegrable_const.add (hpow.const_mul kappa)
  have hmajor : IntervalIntegrable
      (fun s : ℝ => (M * D) * (Real.sqrt r + kappa * Real.rpow s (-1 / 2 : ℝ)))
      volume 0 r := hq.const_mul (M * D)
  rw [compactRadialComplexKernel_integral_eq_radial hr (measurable_helmholtzResolventB r lam)
    (intervalIntegrable_weighted_helmholtzResolventB hr lam) hu x]
  have hpoint : ∀ᵐ s : ℝ, s ∈ Ioc (0 : ℝ) r →
      ‖(2 * (Real.pi : ℂ) * (s : ℂ)) * helmholtzResolventB r lam s * circularMean u s x‖ ≤
      (M * D) * (Real.sqrt r + kappa * Real.rpow s (-1 / 2 : ℝ)) := by
    filter_upwards with s hs
    have hb := helmholtzResolventB_weighted_principal_bound hlam hL hr hs.1 hs.2
    have hm := norm_circularMean_le_closedBall_bound x hs.1.le hs.2 hM
    have h2π : 0 ≤ (2 : ℝ) * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
    have hcoef : 0 ≤ (2 * Real.pi * s) * ‖helmholtzResolventB r lam s‖ :=
      mul_nonneg (mul_nonneg h2π hs.1.le) (norm_nonneg _)
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos hs.1]
    calc
      _ ≤ ((2 * Real.pi * s) * ‖helmholtzResolventB r lam s‖) * M :=
        mul_le_mul_of_nonneg_left hm hcoef
      _ ≤ (D * (Real.sqrt r + kappa * Real.rpow s (-1 / 2 : ℝ))) * M :=
        mul_le_mul_of_nonneg_right hb hMpos.le
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le hr.le hpoint hmajor
  have heval : (∫ s : ℝ in (0 : ℝ)..r,
      (M * D) * (Real.sqrt r + kappa * Real.rpow s (-1 / 2 : ℝ))) =
      (32 * M * (1 + kappa / r) * (r + 2 * kappa)) *
        Real.exp (r * lam.im) / ‖lam‖ := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const (hpow.const_mul kappa),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_rpow_neg_half_zero_radius]
    simp only [sub_zero, smul_eq_mul]
    dsimp [D]
    field_simp [hr.ne', (show ‖lam‖ ≠ 0 by linarith), (Real.sqrt_pos.mpr hr).ne']
  rw [heval] at hi
  exact hi

/-- The requested local convolution estimate, with a genuinely positive
constant chosen from continuity on the fixed compact translated ball. -/
theorem resolventB_principal_convolution_bound {u : Plane → ℂ} (hu : Continuous u)
    (x : Plane) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℂ, ClosedPrincipalSector lam → 1 ≤ ‖lam‖ →
      ‖∫ y : Plane, compactRadialComplexKernel r (helmholtzResolventB r lam) y * u (x - y)‖ ≤
        C * Real.exp (r * lam.im) / ‖lam‖ := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hu.continuousOn
  let M : ℝ := max K 1
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right K 1)
  have hM : ∀ y ∈ Metric.closedBall x r, ‖u y‖ ≤ M :=
    fun y hy => (hK y hy).trans (le_max_left K 1)
  refine ⟨32 * M * (1 + kappa / r) * (r + 2 * kappa), ?_, ?_⟩
  · have hk := kappa_pos
    positivity
  · intro lam hlam hL
    exact resolventB_principal_convolution_bound_of_closedBall_bound hu x hr hMpos hM hlam hL

end J0RadialUniqueness
