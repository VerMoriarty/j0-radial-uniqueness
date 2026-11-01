import Solutions.J0RadialUniqueness.K0SeriesAnalytic
import Solutions.J0RadialUniqueness.QAnalytic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The exact logarithmic constant at the positive real endpoint for the
independently defined K₀ series. No Laplace/Bessel identification is used.
-/

noncomputable section

open Filter
open scoped Topology

namespace J0RadialUniqueness

theorem square_log_half_tendsto_zero :
    Tendsto (fun x : ℝ => x ^ 2 * Real.log (x / 2)) (𝓝[>] 0) (𝓝 0) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hlog : Tendsto (fun x : ℝ => Real.log x * x ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using
      (tendsto_log_mul_rpow_nhdsGT_zero (r := (2 : ℝ)) (by norm_num))
  have hpoly : Tendsto (fun x : ℝ => x ^ 2 * Real.log 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hx.pow 2).mul_const (Real.log 2)
  have h : Tendsto (fun x : ℝ => Real.log x * x ^ 2 - x ^ 2 * Real.log 2)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hlog.sub hpoly
  apply h.congr'
  filter_upwards [show ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x from self_mem_nhdsWithin] with x hx0
  rw [Real.log_div hx0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem complex_quadratic_log_half_tendsto_zero :
    Tendsto (fun x : ℝ => ((x : ℂ) ^ 2 / 4) * (Real.log (x / 2) : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  have h := square_log_half_tendsto_zero.ofReal.div_const (4 : ℂ)
  have hfun : (fun x : ℝ => ((x ^ 2 * Real.log (x / 2) : ℝ) : ℂ) / 4) =
      (fun x : ℝ => ((x : ℂ) ^ 2 / 4) * (Real.log (x / 2) : ℂ)) := by
    funext x
    push_cast
    ring
  rw [hfun] at h
  simpa using h

/-- The logarithmic cancellation is exact, with the actual series Q controlling
the remaining factor. -/
theorem K0Series_real_renormalized_eq {x : ℝ} (hx : 0 < x) :
    K0Series (x : ℂ) + (Real.log (x / 2) : ℂ) =
      -(((x : ℂ) ^ 2 / 4) * (Real.log (x / 2) : ℂ) * Q ((x : ℂ) ^ 2 / 4)) -
        (Real.eulerMascheroniConstant : ℂ) * F ((x : ℂ) ^ 2 / 4) +
          harmonicF ((x : ℂ) ^ 2 / 4) := by
  let u : ℂ := (x : ℂ) ^ 2 / 4
  let l : ℂ := (Real.log (x / 2) : ℂ)
  have hlog : Complex.log ((x : ℂ) / 2) = l := by
    have hx2 : 0 ≤ x / 2 := (div_pos hx (by norm_num : (0 : ℝ) < 2)).le
    simpa only [l, Complex.ofReal_div, Complex.ofReal_ofNat] using
      (Complex.ofReal_log hx2).symm
  change -(Complex.log ((x : ℂ) / 2) + (Real.eulerMascheroniConstant : ℂ)) * F u +
      harmonicF u + l = -(u * l * Q u) - (Real.eulerMascheroniConstant : ℂ) * F u +
        harmonicF u
  rw [hlog]
  calc
    -(l + (Real.eulerMascheroniConstant : ℂ)) * F u + harmonicF u + l =
        -l * (F u - 1) - (Real.eulerMascheroniConstant : ℂ) * F u + harmonicF u := by ring
    _ = -(u * l * Q u) - (Real.eulerMascheroniConstant : ℂ) * F u + harmonicF u := by
      rw [F_sub_one]
      ring

/-- The exact positive-real logarithmic boundary condition for the actual K₀ series. -/
theorem K0Series_positive_real_limit :
    Tendsto (fun x : ℝ => K0Series (x : ℂ) + (Real.log (x / 2) : ℂ))
      (𝓝[>] 0) (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ => (x : ℂ) ^ 2 / 4) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    simpa using (hx.ofReal.pow 2).div_const (4 : ℂ)
  have hQ : Tendsto (fun x : ℝ => Q ((x : ℂ) ^ 2 / 4))
      (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, Q_zero] using (Q_continuous.tendsto 0).comp hu
  have hF : Tendsto (fun x : ℝ => F ((x : ℂ) ^ 2 / 4))
      (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, F_zero] using (F_differentiable.continuous.tendsto 0).comp hu
  have hB : Tendsto (fun x : ℝ => harmonicF ((x : ℂ) ^ 2 / 4))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, harmonicF_zero] using
      (harmonicF_differentiable.continuous.tendsto 0).comp hu
  have hc : Tendsto (fun _ : ℝ => (Real.eulerMascheroniConstant : ℂ))
      (𝓝[>] 0) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := tendsto_const_nhds
  have hmain : Tendsto
      (fun x : ℝ =>
        -(((x : ℂ) ^ 2 / 4) * (Real.log (x / 2) : ℂ) * Q ((x : ℂ) ^ 2 / 4)) -
          (Real.eulerMascheroniConstant : ℂ) * F ((x : ℂ) ^ 2 / 4) +
            harmonicF ((x : ℂ) ^ 2 / 4))
      (𝓝[>] 0) (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
    simpa using
      ((complex_quadratic_log_half_tendsto_zero.mul hQ).neg.sub (hc.mul hF)).add hB
  apply hmain.congr'
  filter_upwards [show ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x from self_mem_nhdsWithin] with x hx0
  exact (K0Series_real_renormalized_eq hx0).symm

end J0RadialUniqueness
