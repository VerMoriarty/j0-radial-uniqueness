import Solutions.J0RadialUniqueness.K0SeriesAnalytic

/-! The independent K₀ series takes real values on the positive real axis. -/

noncomputable section

namespace J0RadialUniqueness

theorem F_ofReal_im (x : ℝ) : (F (x : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa only [Complex.conj_ofReal] using (F_conj (x : ℂ)).symm

theorem F_ofReal_real_value (x : ℝ) : ((F (x : ℂ)).re : ℂ) = F (x : ℂ) := by
  apply Complex.ext
  · simp
  · simp [F_ofReal_im]

theorem harmonicF_ofReal_im (x : ℝ) : (harmonicF (x : ℂ)).im = 0 := by
  unfold harmonicF
  rw [Complex.im_tsum (harmonic_fTerm_summable (x : ℂ))]
  have hfun : (fun n : ℕ => ((harmonic n : ℂ) * fTerm (x : ℂ) n).im) =
      fun _ => (0 : ℝ) := by
    funext n
    have hterm : (harmonic n : ℂ) * fTerm (x : ℂ) n =
        (((harmonic n : ℝ) * (x ^ n / (n.factorial : ℝ) ^ 2) : ℝ) : ℂ) := by
      simp [fTerm]
    rw [hterm, Complex.ofReal_im]
  rw [hfun]
  simp

theorem harmonicF_ofReal_real_value (x : ℝ) :
    ((harmonicF (x : ℂ)).re : ℂ) = harmonicF (x : ℂ) := by
  apply Complex.ext
  · simp
  · simp [harmonicF_ofReal_im]

theorem K0Series_ofReal_im {x : ℝ} (hx : 0 < x) : (K0Series (x : ℂ)).im = 0 := by
  have hu : (x : ℂ) ^ 2 / 4 = ((x ^ 2 / 4 : ℝ) : ℂ) := by push_cast; rfl
  have hlog : Complex.log ((x : ℂ) / 2) = (Real.log (x / 2) : ℂ) := by
    have hx2 : 0 ≤ x / 2 := (div_pos hx (by norm_num : (0 : ℝ) < 2)).le
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using (Complex.ofReal_log hx2).symm
  change (-(Complex.log ((x : ℂ) / 2) + (Real.eulerMascheroniConstant : ℂ)) *
    F ((x : ℂ) ^ 2 / 4) + harmonicF ((x : ℂ) ^ 2 / 4)).im = 0
  rw [hu, hlog]
  simp only [Complex.add_im, Complex.mul_im, Complex.neg_im, Complex.add_re,
    Complex.ofReal_im, Complex.ofReal_re, Complex.neg_re, F_ofReal_im,
    harmonicF_ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, neg_zero]

/-- This is directly the bridge `↑(realK0Series x) = K0Series ↑x` after unfolding
the real-part wrapper used by the real ODE module. -/
theorem K0Series_ofReal_real_value {x : ℝ} (hx : 0 < x) :
    ((K0Series (x : ℂ)).re : ℂ) = K0Series (x : ℂ) := by
  apply Complex.ext
  · simp
  · simp [K0Series_ofReal_im hx]

end J0RadialUniqueness
