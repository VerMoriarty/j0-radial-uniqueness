import Solutions.J0RadialUniqueness.LocalResolventQuotient
import Solutions.J0RadialUniqueness.ResolventQuotientEstimates

/-! Actual boundary estimates for the filled local resolvent quotient. The
compact part is bounded by continuity of the proved entire quotient; the
unbounded parts use the genuine integral estimates, with conjugation of the
input function when a parameter lies below the real axis. -/

noncomputable section

open MeasureTheory Filter Set
open scoped ComplexConjugate Topology ContDiff

namespace J0RadialUniqueness

theorem localConvolution_planarGreen_conj (r : ℝ) (u : Plane → ℂ) (x : Plane) :
    localConvolution (planarGreenKernel r) (fun y => conj (u y)) x =
      conj (localConvolution (planarGreenKernel r) u x) := by
  unfold localConvolution
  rw [← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by simp only [Complex.real_smul, map_mul, Complex.conj_ofReal])

theorem mass_ne_zero_of_mean_defect_ne_zero {r : ℝ} {lam : ℂ}
    (hdefect : 1 - J0 ((r : ℂ) * lam) ≠ 0) : helmholtzResolventMass r lam ≠ 0 := by
  intro hzero
  apply hdefect
  rw [← helmholtzResolventMass_mul_parameter_sq, hzero, mul_zero]

theorem mean_defect_ne_zero_of_spectral_lower {z : ℂ} (hnorm : 0 < ‖z‖)
    (hden : (1 + Real.exp z.im / Real.sqrt (2 * Real.pi * ‖z‖)) / 4 ≤ ‖1 - J0 z‖) :
    1 - J0 z ≠ 0 := by
  have hD : 0 < Real.sqrt (2 * Real.pi * ‖z‖) :=
    Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) hnorm)
  exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hden)

theorem filled_quotient_norm_le_of_ordinary {r : ℝ} {u : Plane → ℂ} {x : Plane}
    {lam : ℂ} {K : ℝ} (hdefect : 1 - J0 ((r : ℂ) * lam) ≠ 0)
    (hbound : ‖planarResolventTConvolution r u x lam / helmholtzResolventMass r lam‖ ≤ K) :
    ‖localResolventQuotient r u x lam‖ ≤ K := by
  rw [localResolventQuotient_eq_div r u x (mass_ne_zero_of_mean_defect_ne_zero hdefect)]
  exact hbound

theorem filled_quotient_norm_le_of_conjugate_ordinary {r : ℝ} {u : Plane → ℂ} {x : Plane}
    {lam : ℂ} {K : ℝ} (hdefect : 1 - J0 ((r : ℂ) * conj lam) ≠ 0)
    (hbound : ‖planarResolventTConvolution r (fun y => conj (u y)) x (conj lam) /
      helmholtzResolventMass r (conj lam)‖ ≤ K) :
    ‖localResolventQuotient r u x lam‖ ≤ K := by
  have hmconj := mass_ne_zero_of_mean_defect_ne_zero hdefect
  have hmass : helmholtzResolventMass r lam ≠ 0 := by
    intro hzero
    apply hmconj
    rw [helmholtzResolventMass_conj, hzero, map_zero]
  rw [localResolventQuotient_eq_div r u x hmass]
  have he := norm_ordinaryResolventQuotient_conj r u x (conj lam)
  simpa only [starRingEnd_self_apply] using he.le.trans hbound

theorem right_diagonal_principal_cases {lam : ℂ} (hdiag : |lam.im| = |lam.re|)
    (hre : 0 ≤ lam.re) (hnorm : 0 < ‖lam‖) :
    (ClosedPrincipalSector lam ∧ lam.im = lam.re) ∨
      (ClosedPrincipalSector (conj lam) ∧ (conj lam).im = (conj lam).re) := by
  have hnormle := Complex.norm_le_abs_re_add_abs_im lam
  rw [hdiag, abs_of_nonneg hre] at hnormle
  have hre' : 0 < lam.re := by linarith
  rw [abs_of_nonneg hre] at hdiag
  rcases le_total 0 lam.im with hi | hi
  · rw [abs_of_nonneg hi] at hdiag
    exact Or.inl ⟨⟨hi, hdiag.le, hre'⟩, hdiag⟩
  · rw [abs_of_nonpos hi] at hdiag
    right
    simp only [Complex.conj_re, Complex.conj_im]
    exact ⟨⟨by simpa only [Complex.conj_im] using neg_nonneg.mpr hi, hdiag.le, hre'⟩, hdiag⟩

theorem right_vertical_principal_cases {lam : ℂ} {N : ℝ}
    (hN : 0 < N) (hre : lam.re = N) (him : |lam.im| ≤ N) :
    ClosedPrincipalSector lam ∨ ClosedPrincipalSector (conj lam) := by
  rcases le_total 0 lam.im with hi | hi
  · left
    exact ⟨hi, by simpa only [hre] using (le_abs_self lam.im).trans him,
      by simpa only [hre] using hN⟩
  · right
    simp only [ClosedPrincipalSector, Complex.conj_re, Complex.conj_im]
    exact ⟨by linarith, by simpa only [hre] using (neg_le_abs lam.im).trans him,
      by simpa only [hre] using hN⟩

/-- A simultaneous large-parameter estimate on the diagonal and vertical
boundary pieces in the full right half-plane. -/
theorem localResolventQuotient_large_boundary_bound {r : ℝ} (hr : 0 < r)
    {u : Plane → ℂ} (hu : Continuous u) (x : Plane)
    (hgreen : localConvolution (planarGreenKernel r) u x = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ lam : ℂ, 0 ≤ lam.re → 1 ≤ ‖lam‖ →
      ((|lam.im| = |lam.re| ∧ 10000 ≤ r * ‖lam‖) ∨
        (∃ n : ℕ, (((r : ℂ) * lam).re = 2 * Real.pi * (n : ℝ) + 3 * Real.pi / 4) ∧
          |lam.im| ≤ lam.re ∧ 256 ≤ r * ‖lam‖)) →
      ‖localResolventQuotient r u x lam‖ ≤ K := by
  have huc : Continuous (fun y => conj (u y)) := Complex.continuous_conj.comp hu
  have hGc : localConvolution (planarGreenKernel r) (fun y => conj (u y)) x = 0 := by
    rw [localConvolution_planarGreen_conj, hgreen, map_zero]
  obtain ⟨Kp, hKp, hp⟩ := planarResolventTConvolution_div_mass_geometric_uniform_bound hr hu x hgreen
  obtain ⟨Km, hKm, hm⟩ := planarResolventTConvolution_div_mass_geometric_uniform_bound hr huc x hGc
  refine ⟨max Kp Km, lt_of_lt_of_le hKp (le_max_left _ _), ?_⟩
  intro lam hre hL hgeometry
  have hnorm : 0 < ‖lam‖ := by linarith
  have hscaled : 0 < ‖(r : ℂ) * lam‖ := by rw [norm_real_mul_parameter hr]; positivity
  have hscaledc : 0 < ‖(r : ℂ) * conj lam‖ := by
    rw [norm_real_mul_parameter hr, Complex.norm_conj]
    positivity
  rcases hgeometry with ⟨hdiag, hρ⟩ | ⟨n, hline, hsector, hρ⟩
  · rcases right_diagonal_principal_cases hdiag hre hnorm with ⟨hsec, hd⟩ | ⟨hsec, hd⟩
    · have hdscale : ((r : ℂ) * lam).im = ((r : ℂ) * lam).re := by
        simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, mul_zero, add_zero, sub_zero, hd]
      have hden := spectral_positive_diagonal_bound (closedPrincipalSector_pos_scale hsec hr)
        hdscale (by simpa only [norm_real_mul_parameter hr] using hρ)
      exact (filled_quotient_norm_le_of_ordinary (mean_defect_ne_zero_of_spectral_lower hscaled hden)
        (hp lam hsec hL (Or.inr ⟨hdscale, hρ⟩))).trans (le_max_left _ _)
    · have hdscale : ((r : ℂ) * conj lam).im = ((r : ℂ) * conj lam).re := by
        simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, mul_zero, add_zero, sub_zero, hd]
      have hρc : 10000 ≤ r * ‖conj lam‖ := by simpa only [Complex.norm_conj] using hρ
      have hden := spectral_positive_diagonal_bound (closedPrincipalSector_pos_scale hsec hr)
        hdscale (by simpa only [norm_real_mul_parameter hr] using hρc)
      exact (filled_quotient_norm_le_of_conjugate_ordinary
        (mean_defect_ne_zero_of_spectral_lower hscaledc hden)
        (hm (conj lam) hsec (by simpa only [Complex.norm_conj] using hL)
          (Or.inr ⟨hdscale, hρc⟩))).trans (le_max_right _ _)
  · have hre' : 0 < lam.re := by
      have hnormle := Complex.norm_le_abs_re_add_abs_im lam
      rw [abs_of_nonneg hre] at hnormle
      linarith
    rcases right_vertical_principal_cases hre' rfl hsector with hsec | hsec
    · have hden := spectral_vertical_bound (closedPrincipalSector_pos_scale hsec hr) n hline
        (by simpa only [norm_real_mul_parameter hr] using hρ)
      exact (filled_quotient_norm_le_of_ordinary (mean_defect_ne_zero_of_spectral_lower hscaled hden)
        (hp lam hsec hL (Or.inl ⟨n, hline, hρ⟩))).trans (le_max_left _ _)
    · have hlinec : ((r : ℂ) * conj lam).re = 2 * Real.pi * (n : ℝ) + 3 * Real.pi / 4 := by
        simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero, Complex.conj_re] using hline
      have hρc : 256 ≤ r * ‖conj lam‖ := by simpa only [Complex.norm_conj] using hρ
      have hden := spectral_vertical_bound (closedPrincipalSector_pos_scale hsec hr) n hlinec
        (by simpa only [norm_real_mul_parameter hr] using hρc)
      exact (filled_quotient_norm_le_of_conjugate_ordinary
        (mean_defect_ne_zero_of_spectral_lower hscaledc hden)
        (hm (conj lam) hsec (by simpa only [Complex.norm_conj] using hL)
          (Or.inl ⟨n, hlinec, hρc⟩))).trans (le_max_right _ _)

def resolventVerticalSequence (r : ℝ) (N₀ : ℕ) (n : ℕ) : ℝ :=
  (2 * Real.pi * ((n : ℝ) + (N₀ : ℝ)) + 3 * Real.pi / 4) / r

theorem resolventVerticalSequence_phase {r : ℝ} (hr : 0 < r) (N₀ n : ℕ) :
    r * resolventVerticalSequence r N₀ n =
      2 * Real.pi * ((n + N₀ : ℕ) : ℝ) + 3 * Real.pi / 4 := by
  dsimp [resolventVerticalSequence]
  field_simp [hr.ne'] <;> push_cast <;> ring

theorem resolventVerticalSequence_tendsto {r : ℝ} (hr : 0 < r) (N₀ : ℕ) :
    Tendsto (resolventVerticalSequence r N₀) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ) / r) ?_
    ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_div_const hr)
  intro n
  change (n : ℝ) / r ≤ (2 * Real.pi * ((n : ℝ) + (N₀ : ℝ)) + 3 * Real.pi / 4) / r
  apply div_le_div_of_nonneg_right _ hr.le
  have hp : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hp' := mul_le_mul_of_nonneg_right hp
    (add_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀))
  nlinarith [Real.pi_pos, (Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)]

theorem exists_resolventVerticalSequence_large {r : ℝ} (hr : 0 < r) :
    ∃ N₀ : ℕ, ∀ n : ℕ,
      1 ≤ resolventVerticalSequence r N₀ n ∧ 256 ≤ r * resolventVerticalSequence r N₀ n := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max r 256)
  refine ⟨N₀, ?_⟩
  intro n
  have hphase := resolventVerticalSequence_phase hr N₀ n
  have hp : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hp' := mul_le_mul_of_nonneg_right hp
    (add_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀))
  have hNr : r < (N₀ : ℝ) := lt_of_le_of_lt (le_max_left r 256) hN₀
  have hN256 : (256 : ℝ) < (N₀ : ℝ) := lt_of_le_of_lt (le_max_right r 256) hN₀
  have hangle : (N₀ : ℝ) ≤ 2 * Real.pi * ((n + N₀ : ℕ) : ℝ) + 3 * Real.pi / 4 := by
    push_cast
    nlinarith [Real.pi_pos, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  constructor
  · have hmul : r ≤ r * resolventVerticalSequence r N₀ n := by rw [hphase]; linarith
    exact (mul_le_mul_iff_right₀ hr).mp (by simpa only [mul_one] using hmul)
  · rw [hphase]
    linarith

/-- Decay at the positive real sampling points of any sufficiently shifted
actual spectral vertical sequence. -/
theorem localResolventQuotient_real_sequence_decay {r : ℝ} (hr : 0 < r)
    {u : Plane → ℂ} (hu : Continuous u) (x : Plane)
    (hgreen : localConvolution (planarGreenKernel r) u x = 0) (N₀ : ℕ)
    (hlarge : ∀ n : ℕ, 1 ≤ resolventVerticalSequence r N₀ n ∧
      256 ≤ r * resolventVerticalSequence r N₀ n) :
    ∃ D : ℝ, 0 < D ∧
      (∀ n : ℕ, ‖localResolventQuotient r u x (resolventVerticalSequence r N₀ n : ℂ)‖ ≤
        D / Real.sqrt (resolventVerticalSequence r N₀ n)) ∧
      Tendsto (fun n : ℕ => localResolventQuotient r u x
        (resolventVerticalSequence r N₀ n : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hdecay⟩ := planarResolventTConvolution_div_mass_vertical_bound hr hu x hgreen
  let D : ℝ := 4 * C * Real.sqrt (2 * Real.pi * r)
  have hD : 0 < D := by dsimp [D]; positivity
  have hsample (n : ℕ) :
      ‖localResolventQuotient r u x (resolventVerticalSequence r N₀ n : ℂ)‖ ≤
        D / Real.sqrt (resolventVerticalSequence r N₀ n) := by
    let N : ℝ := resolventVerticalSequence r N₀ n
    have hN : 1 ≤ N := (hlarge n).1
    have hNpos : 0 < N := by linarith
    have hsec : ClosedPrincipalSector (N : ℂ) := by
      simp only [ClosedPrincipalSector, Complex.ofReal_im, Complex.ofReal_re]
      exact ⟨le_refl 0, hNpos.le, hNpos⟩
    have hnorm : ‖(N : ℂ)‖ = N := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNpos]
    have hline : (((r : ℂ) * (N : ℂ)).re) =
        2 * Real.pi * ((n + N₀ : ℕ) : ℝ) + 3 * Real.pi / 4 := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        using resolventVerticalSequence_phase hr N₀ n
    have hρ : 256 ≤ r * ‖(N : ℂ)‖ := by rw [hnorm]; exact (hlarge n).2
    have hden := spectral_vertical_bound (closedPrincipalSector_pos_scale hsec hr) (n + N₀) hline
      (by simpa only [norm_real_mul_parameter hr] using hρ)
    have hscaled : 0 < ‖(r : ℂ) * (N : ℂ)‖ := by rw [norm_real_mul_parameter hr, hnorm]; positivity
    have hb := filled_quotient_norm_le_of_ordinary
      (mean_defect_ne_zero_of_spectral_lower hscaled hden)
      (hdecay (N : ℂ) hsec (by simpa only [hnorm] using hN) (n + N₀) hline hρ)
    simpa only [hnorm, D, N] using hb
  refine ⟨D, hD, hsample, ?_⟩
  exact squeeze_zero_norm hsample
    ((Real.tendsto_sqrt_atTop.comp (resolventVerticalSequence_tendsto hr N₀)).const_div_atTop D)

/-- The only continuity input in this general boundary construction concerns
the actual filled quotient. The smooth-core wrapper below discharges it. -/
theorem localResolventQuotient_boundary_bounds_of_continuous {r : ℝ} (hr : 0 < r)
    {u : Plane → ℂ} (hu : Continuous u) (x : Plane)
    (hgreen : localConvolution (planarGreenKernel r) u x = 0)
    (hq : Continuous (localResolventQuotient r u x)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
      Tendsto (resolventVerticalSequence r N₀) atTop atTop ∧
      (∀ lam : ℂ, |lam.im| = |lam.re| → ‖localResolventQuotient r u x lam‖ ≤ C) ∧
      (∀ n : ℕ, ∀ lam : ℂ, lam.re = resolventVerticalSequence r N₀ n →
        |lam.im| ≤ resolventVerticalSequence r N₀ n → ‖localResolventQuotient r u x lam‖ ≤ C) ∧
      Tendsto (fun n : ℕ => localResolventQuotient r u x
        (resolventVerticalSequence r N₀ n : ℂ)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hboundary⟩ := localResolventQuotient_large_boundary_bound hr hu x hgreen
  let T : ℝ := max 1 (10000 / r)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) T).exists_bound_of_continuousOn hq.continuousOn
  let C : ℝ := max M K
  have hC : 0 < C := lt_of_lt_of_le hK (le_max_right _ _)
  obtain ⟨N₀, hN₀⟩ := exists_resolventVerticalSequence_large hr
  obtain ⟨D, hD, hsample, hlim⟩ := localResolventQuotient_real_sequence_decay hr hu x hgreen N₀ hN₀
  refine ⟨C, hC, N₀, resolventVerticalSequence_tendsto hr N₀, ?_, ?_, hlim⟩
  · intro lam hdiag
    by_cases hsmall : ‖lam‖ ≤ T
    · exact (hM lam (by simpa only [Metric.mem_closedBall, dist_zero_right] using hsmall)).trans
        (le_max_left _ _)
    · have hnorm : T < ‖lam‖ := lt_of_not_ge hsmall
      have hL : 1 ≤ ‖lam‖ := (le_max_left 1 (10000 / r)).trans hnorm.le
      have hρ : 10000 ≤ r * ‖lam‖ := by
        have h := (div_le_iff₀ hr).mp ((le_max_right 1 (10000 / r)).trans hnorm.le)
        nlinarith
      rcases le_total 0 lam.re with hre | hre
      · exact (hboundary lam hre hL (Or.inl ⟨hdiag, hρ⟩)).trans (le_max_right _ _)
      · have hb := hboundary (-lam) (by simpa only [Complex.neg_re] using neg_nonneg.mpr hre)
          (by simpa only [norm_neg] using hL)
          (Or.inl ⟨by simpa only [Complex.neg_im, Complex.neg_re, abs_neg] using hdiag,
            by simpa only [norm_neg] using hρ⟩)
        rw [localResolventQuotient_neg hr hu x] at hb
        exact hb.trans (le_max_right _ _)
  · intro n lam hre him
    have hN : 1 ≤ resolventVerticalSequence r N₀ n := (hN₀ n).1
    have hNpos : 0 < resolventVerticalSequence r N₀ n := by linarith
    have hnormN : resolventVerticalSequence r N₀ n ≤ ‖lam‖ := by
      simpa only [hre] using Complex.re_le_norm lam
    have hline : ((r : ℂ) * lam).re =
        2 * Real.pi * ((n + N₀ : ℕ) : ℝ) + 3 * Real.pi / 4 := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre]
        using resolventVerticalSequence_phase hr N₀ n
    have hρ : 256 ≤ r * ‖lam‖ := (hN₀ n).2.trans (mul_le_mul_of_nonneg_left hnormN hr.le)
    exact (hboundary lam (by rw [hre]; exact hNpos.le) (hN.trans hnormN)
      (Or.inr ⟨n + N₀, hline, by simpa only [hre] using him, hρ⟩)).trans (le_max_right _ _)

/-- Actual boundary control for the entire local quotient under the full local
two-filter hypotheses. No analytic or growth assertion is left as a premise. -/
theorem localResolventQuotient_boundary_bounds {u : Plane → ℂ} (hu : ContDiff ℝ ∞ u)
    {R r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hR : r₁ + r₂ < R)
    (hNoCommon : ∀ lam : ℂ,
      helmholtzResolventMass r₁ lam ≠ 0 ∨ helmholtzResolventMass r₂ lam ≠ 0)
    (hG₁ : ∀ x ∈ planeBall (R - r₁), localConvolution (planarGreenKernel r₁) u x = 0)
    (hG₂ : ∀ x ∈ planeBall (R - r₂), localConvolution (planarGreenKernel r₂) u x = 0)
    {x : Plane} (hx : x ∈ planeBall (R - r₁)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
      Tendsto (resolventVerticalSequence r₁ N₀) atTop atTop ∧
      (∀ lam : ℂ, |lam.im| = |lam.re| → ‖localResolventQuotient r₁ u x lam‖ ≤ C) ∧
      (∀ n : ℕ, ∀ lam : ℂ, lam.re = resolventVerticalSequence r₁ N₀ n →
        |lam.im| ≤ resolventVerticalSequence r₁ N₀ n → ‖localResolventQuotient r₁ u x lam‖ ≤ C) ∧
      Tendsto (fun n : ℕ => localResolventQuotient r₁ u x
        (resolventVerticalSequence r₁ N₀ n : ℂ)) atTop (𝓝 0) := by
  exact localResolventQuotient_boundary_bounds_of_continuous hr₁ hu.continuous x (hG₁ x hx)
    (localResolventQuotient_differentiable hu hr₁ hr₂ hR hNoCommon hG₁ hG₂ hx).continuous

end J0RadialUniqueness
