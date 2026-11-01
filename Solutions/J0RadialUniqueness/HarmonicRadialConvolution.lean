import Solutions.J0RadialUniqueness.MollifiedWeakHarmonic
import Solutions.J0RadialUniqueness.CircularMeanRegularity
import Solutions.J0RadialUniqueness.PlaneHarmonicMeanValue
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Polar integration and reproduction by radial smoothing kernels.  The
reproduction theorem uses the actual circular mean, and the polar Fubini
integrability condition is proved from compact support of the kernel. -/

noncomputable section

open MeasureTheory Set
open scoped ContDiff Topology

namespace J0RadialUniqueness

def planePolar (p : ℝ × ℝ) : Plane :=
  Complex.orthonormalBasisOneI.repr (Complex.polarCoord.symm p)

theorem planePolar_eq (p : ℝ × ℝ) : planePolar p = p.1 • circleDirection p.2 := by
  ext i
  fin_cases i <;>
    simp [planePolar, Complex.polarCoord_symm_apply, circleDirection,
      Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem continuous_planePolar : Continuous planePolar := by
  have hfun : planePolar = fun p : ℝ × ℝ => p.1 • circleDirection p.2 :=
    funext planePolar_eq
  rw [hfun]
  exact continuous_fst.smul (continuous_circleDirection.comp continuous_snd)

@[simp] theorem norm_planePolar (p : ℝ × ℝ) : ‖planePolar p‖ = |p.1| := by
  rw [planePolar_eq]
  simp [norm_smul]

section PolarIntegral

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The polar change of variables for actual plane volume. -/
theorem plane_integral_eq_polar (F : Plane → V) :
    (∫ y : Plane, F y) =
      ∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • F (planePolar p) ∂(volume.prod volume) := by
  have he := Complex.orthonormalBasisOneI.measurePreserving_repr
  have hi : (∫ z : ℂ, F (Complex.orthonormalBasisOneI.repr z)) = ∫ y : Plane, F y :=
    he.integral_comp Complex.orthonormalBasisOneI.repr.toMeasurableEquiv.measurableEmbedding F
  rw [← hi]
  simpa only [planePolar, polarCoord_target, Measure.volume_eq_prod] using
    (Complex.integral_comp_polarCoord_symm
      (fun z : ℂ => F (Complex.orthonormalBasisOneI.repr z))).symm

/-- The polar integrand is genuinely integrable. Its support on the polar
target fits in a compact rectangle, including the potentially singular endpoint
`r = 0`. -/
theorem plane_polar_integrable {F : Plane → V} (hF : Continuous F)
    (hc : HasCompactSupport F) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • F (planePolar p))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
  obtain ⟨R, hRpos, hR⟩ := hc.isCompact.isBounded.subset_ball_lt 0 (0 : Plane)
  have hP : Continuous (fun p : ℝ × ℝ => p.1 • F (planePolar p)) :=
    continuous_fst.smul (hF.comp continuous_planePolar)
  have hK := hP.continuousOn.integrableOn_compact
    (μ := (volume : Measure (ℝ × ℝ)))
    (isCompact_Icc.prod (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi)))
      (K := Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi)
  have hK' : IntegrableOn (fun p : ℝ × ℝ => p.1 • F (planePolar p))
      (Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hK
  apply IntegrableOn.of_inter_support (measurableSet_Ioi.prod measurableSet_Ioo)
  apply hK'.mono_set
  rintro p ⟨⟨hr, hθ⟩, hsupport⟩
  have hnz : F (planePolar p) ≠ 0 := by
    intro hzero
    exact hsupport (by simp only [hzero, smul_zero])
  have hnorm : p.1 < R := by
    have hball := hR (subset_closure hnz)
    simpa only [Metric.mem_ball, dist_zero_right, norm_planePolar,
      abs_of_pos (show 0 < p.1 from hr)] using hball
  exact ⟨⟨hr.le, hnorm.le⟩, ⟨hθ.1.le, hθ.2.le⟩⟩

theorem twoPi_periodic_circleDirection : Function.Periodic circleDirection (2 * Real.pi) := by
  intro t
  ext i
  fin_cases i <;> simp [circleDirection, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The interval used by polar coordinates gives the same actual mean as the
paper's interval `(0, 2π)`. No change of representatives is involved. -/
theorem centeredAngleIntegral_eq_circularMean (g : Plane → V) (r : ℝ) (x : Plane) :
    (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, g (x + r • circleDirection θ)) =
      (2 * Real.pi) • circularMean g r x := by
  have hperiod : Function.Periodic (fun θ : ℝ => g (x + r • circleDirection θ))
      (2 * Real.pi) := by
    intro θ
    change g (x + r • circleDirection (θ + 2 * Real.pi)) = g (x + r • circleDirection θ)
    rw [twoPi_periodic_circleDirection θ]
  have hshift : (∫ θ in -Real.pi..Real.pi, g (x + r • circleDirection θ)) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, g (x + r • circleDirection θ) := by
    have hπ : -Real.pi + 2 * Real.pi = Real.pi := by ring
    have h := hperiod.intervalIntegral_add_eq (-Real.pi) 0
    simp only [hπ, zero_add] at h
    convert! h using 1 <;> rfl
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]), hshift]
  simp only [circularMean, smul_smul, mul_inv_cancel₀ (ne_of_gt Real.two_pi_pos), one_smul]

theorem circularMean_constant (c : V) (r : ℝ) (x : Plane) :
    circularMean (fun _ : Plane => c) r x = c := by
  simp only [circularMean, intervalIntegral.integral_const, sub_zero, smul_smul,
    inv_mul_cancel₀ (ne_of_gt Real.two_pi_pos), one_smul]

/-- Polar disintegration of a compact radial kernel against a function whose
circular means at `x` equal its value at `x`. The radial coefficient is kept
explicit so that normalization is identified by the constant-function case. -/
theorem radial_weighted_integral_core {g : Plane → V} {φ : Plane → ℝ}
    (hg : Continuous g) (hcφ : HasCompactSupport φ) (hφ : Continuous φ)
    (hradial : ∀ y z : Plane, ‖y‖ = ‖z‖ → φ y = φ z)
    (x : Plane) (hmean : ∀ r : ℝ, circularMean g r x = g x) :
    (∫ y : Plane, φ y • g (x - y)) =
      (∫ r : ℝ in Ioi (0 : ℝ),
        (r * φ (r • circleDirection 0)) * (2 * Real.pi)) • g x := by
  let F : Plane → V := fun y => φ y • g (x - y)
  have hF : Continuous F := hφ.smul (hg.comp (continuous_const.sub continuous_id))
  have hcF : HasCompactSupport F := hcφ.smul_right
  have hPF := plane_polar_integrable hF hcF
  calc
    (∫ y : Plane, φ y • g (x - y)) =
        ∫ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          p.1 • F (planePolar p) ∂(volume.prod volume) :=
      plane_integral_eq_polar F
    _ = ∫ r : ℝ in Ioi (0 : ℝ), ∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
        r • (φ (r • circleDirection θ) • g (x - r • circleDirection θ)) := by
      rw [setIntegral_prod _ hPF]
      simp only [F, planePolar_eq]
    _ = ∫ r : ℝ in Ioi (0 : ℝ), (r * φ (r • circleDirection 0)) •
        (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, g (x + (-r) • circleDirection θ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      change (∫ θ : ℝ in Ioo (-Real.pi) Real.pi,
        r • (φ (r • circleDirection θ) • g (x - r • circleDirection θ))) =
        (r * φ (r • circleDirection 0)) •
          (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, g (x + (-r) • circleDirection θ))
      rw [← integral_smul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ hθ
      change r • (φ (r • circleDirection θ) • g (x - r • circleDirection θ)) =
        (r * φ (r • circleDirection 0)) • g (x + (-r) • circleDirection θ)
      have heq : φ (r • circleDirection θ) = φ (r • circleDirection 0) :=
        hradial _ _ (by simp only [norm_smul, norm_circleDirection])
      rw [heq, smul_smul]
      simp only [neg_smul, sub_eq_add_neg]
    _ = ∫ r : ℝ in Ioi (0 : ℝ),
        ((r * φ (r • circleDirection 0)) * (2 * Real.pi)) • g x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      change (r * φ (r • circleDirection 0)) •
          (∫ θ : ℝ in Ioo (-Real.pi) Real.pi, g (x + (-r) • circleDirection θ)) =
        ((r * φ (r • circleDirection 0)) * (2 * Real.pi)) • g x
      rw [centeredAngleIntegral_eq_circularMean, hmean, smul_smul]
    _ = _ := integral_smul_const _ _

/-- Reproduction by every continuous compact radial kernel, with its true
Lebesgue integral as normalization. -/
theorem radial_weighted_integral {g : Plane → V} {φ : Plane → ℝ}
    (hg : Continuous g) (hcφ : HasCompactSupport φ) (hφ : Continuous φ)
    (hradial : ∀ y z : Plane, ‖y‖ = ‖z‖ → φ y = φ z)
    (x : Plane) (hmean : ∀ r : ℝ, circularMean g r x = g x) :
    (∫ y : Plane, φ y • g (x - y)) = (∫ y : Plane, φ y) • g x := by
  have hc := radial_weighted_integral_core (g := fun _ : Plane => (1 : ℝ))
    continuous_const hcφ hφ hradial x (fun r => circularMean_constant 1 r x)
  simp only [smul_eq_mul, mul_one] at hc
  rw [radial_weighted_integral_core hg hcφ hφ hradial x hmean, ← hc]

end PolarIntegral

theorem mollified_eq_integral_swap (f : Plane → ℂ) (φ : Plane → ℝ) (x : Plane) :
    mollified f φ x = ∫ y : Plane, φ y • f (x - y) := by
  exact convolution_eq_swap realKernelPair

/-- A normalized radial kernel reproduces a continuous function satisfying its
actual circular mean identities. -/
theorem mollified_eq_of_circularMean {g : Plane → ℂ} {φ : Plane → ℝ}
    (hg : Continuous g) (hcφ : HasCompactSupport φ) (hφ : Continuous φ)
    (hradial : ∀ y z : Plane, ‖y‖ = ‖z‖ → φ y = φ z)
    (hnorm : (∫ y : Plane, φ y) = 1)
    (x : Plane) (hmean : ∀ r : ℝ, circularMean g r x = g x) : mollified g φ x = g x := by
  rw [mollified_eq_integral_swap,
    radial_weighted_integral hg hcφ hφ hradial x hmean, hnorm, one_smul]

/-- Smooth harmonic functions are reproduced by normalized compact radial kernels. -/
theorem mollified_eq_of_harmonic {g : Plane → ℂ} {φ : Plane → ℝ}
    (hg : InnerProductSpace.HarmonicOnNhd g Set.univ)
    (hcφ : HasCompactSupport φ) (hφ : Continuous φ)
    (hradial : ∀ y z : Plane, ‖y‖ = ‖z‖ → φ y = φ z)
    (hnorm : (∫ y : Plane, φ y) = 1) (x : Plane) : mollified g φ x = g x := by
  exact mollified_eq_of_circularMean (continuousOn_univ.mp hg.continuousOn)
    hcφ hφ hradial hnorm x (fun r => circularMean_eq_of_harmonicOnNhd g hg r x)

/-- Fixing just one radial kernel is enough: after smoothing a weakly harmonic
function by that kernel, every further compact smoothing agrees with the same
smoothing of the original function. The second kernel need not be radial. -/
theorem mollified_eq_mollified_radial_smoothing {f : Plane → ℂ} {φ ψ : Plane → ℝ}
    (hf : LocallyIntegrable f) (hweak : DistributionHarmonicOn f Set.univ)
    (hcφ : HasCompactSupport φ) (hφ : ContDiff ℝ ∞ φ)
    (hradial : ∀ y z : Plane, ‖y‖ = ‖z‖ → φ y = φ z)
    (hnorm : (∫ y : Plane, φ y) = 1)
    (hcψ : HasCompactSupport ψ) (hψ : ContDiff ℝ ∞ ψ) (x : Plane) :
    mollified f ψ x = mollified (mollified f φ) ψ x := by
  have hh := (mollified_smooth_harmonic hf hweak hcψ hψ).2
  calc
    mollified f ψ x = mollified (mollified f ψ) φ x :=
      (mollified_eq_of_harmonic hh hcφ hφ.continuous hradial hnorm x).symm
    _ = mollified (mollified f φ) ψ x :=
      mollified_mollified_comm hf hcψ hψ.continuous hcφ hφ.continuous x

end J0RadialUniqueness
