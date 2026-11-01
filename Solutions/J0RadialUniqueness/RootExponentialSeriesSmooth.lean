import Solutions.J0RadialUniqueness.BesselCosineSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Actual finite regularity of the root exponential and cosine series.
Uniform majorants are proved on each fixed compact real interval from the
actual root localization. Differentiation of the infinite sum uses a proved
smooth-series theorem with its summability and base-point inputs supplied.
The final residue-coefficient applications discharge the generic weighted
summability conditions. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace J0RadialUniqueness

theorem norm_root_exponential_real_mul_le {σ z : ℂ}
    (hσ : σ = Complex.I ∨ σ = -Complex.I) (hz : z ≠ 0) (hJ : J0 z = 1)
    {T x : ℝ} (hT : 0 ≤ T) (hx : |x| ≤ T) :
    ‖Complex.exp (σ * z * (x : ℂ))‖ ≤ (4 : ℝ) ^ T * ‖z‖ ^ T := by
  have hre : |(σ * z * (x : ℂ)).re| = |z.im| * |x| := by
    rcases hσ with rfl | rfl <;>
      simp [Complex.mul_re, Complex.mul_im, abs_mul]
  have he : Real.exp (T * |z.im|) ≤ (4 * ‖z‖) ^ T := by
    rw [mul_comm T, Real.exp_mul]
    exact Real.rpow_le_rpow (Real.exp_pos _).le
      (one_point_exp_abs_im_bound hz hJ).le hT
  rw [Complex.norm_exp]
  calc
    Real.exp ((σ * z * (x : ℂ)).re) ≤ Real.exp |(σ * z * (x : ℂ)).re| :=
      Real.exp_le_exp.mpr (le_abs_self _)
    _ ≤ Real.exp (T * |z.im|) := by
      apply Real.exp_le_exp.mpr
      rw [hre]
      nlinarith [abs_nonneg z.im]
    _ ≤ _ := he.trans_eq (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (norm_nonneg z))

def rootExponentialDerivativeTerm (a : RightOnePoint → ℂ) (σ : ℂ)
    (k : ℕ) (z : RightOnePoint) (x : ℝ) : ℂ :=
  a z * (σ * (z : ℂ)) ^ k * Complex.exp (σ * (z : ℂ) * (x : ℂ))

def rootExponentialDerivativeSeries (a : RightOnePoint → ℂ) (σ : ℂ)
    (k : ℕ) (x : ℝ) : ℂ :=
  ∑' z : RightOnePoint, rootExponentialDerivativeTerm a σ k z x

theorem rootExponentialDerivativeTerm_hasDerivAt (a : RightOnePoint → ℂ)
    (σ : ℂ) (k : ℕ) (z : RightOnePoint) (x : ℝ) :
    HasDerivAt (rootExponentialDerivativeTerm a σ k z)
      (rootExponentialDerivativeTerm a σ (k + 1) z x) x := by
  have hh := ((((hasDerivAt_id (x : ℂ)).const_mul (σ * (z : ℂ))).cexp).comp_ofReal).const_mul
    (a z * (σ * (z : ℂ)) ^ k)
  convert! hh using 1 <;>
    simp only [rootExponentialDerivativeTerm, id_eq, mul_one, pow_succ] <;>
    first | (funext y; ring) | ring

theorem norm_rootExponentialDerivativeTerm_le (a : RightOnePoint → ℂ)
    {σ : ℂ} (hσ : σ = Complex.I ∨ σ = -Complex.I) (k : ℕ)
    {T x : ℝ} (hT : 0 ≤ T) (hx : |x| ≤ T) (z : RightOnePoint) :
    ‖rootExponentialDerivativeTerm a σ k z x‖ ≤
      (4 : ℝ) ^ T * (‖a z‖ * ‖(z : ℂ)‖ ^ (T + k)) := by
  have hσnorm : ‖σ‖ = 1 := by rcases hσ with rfl | rfl <;> simp
  have hρ : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.val.property.1
  have hh := norm_root_exponential_real_mul_le hσ z.val.property.1 z.val.property.2 hT hx
  unfold rootExponentialDerivativeTerm
  rw [norm_mul, norm_mul, norm_pow, norm_mul, hσnorm, one_mul]
  calc
    _ ≤ (‖a z‖ * ‖(z : ℂ)‖ ^ k) * ((4 : ℝ) ^ T * ‖(z : ℂ)‖ ^ T) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by
      rw [Real.rpow_add hρ, Real.rpow_natCast]
      ring

theorem rootExponentialDerivativeSeries_summable (a : RightOnePoint → ℂ)
    {σ : ℂ} (hσ : σ = Complex.I ∨ σ = -Complex.I) (k : ℕ)
    {T x : ℝ} (hT : 0 ≤ T)
    (hw : Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ (T + k)))
    (hx : |x| ≤ T) :
    Summable (fun z : RightOnePoint => rootExponentialDerivativeTerm a σ k z x) :=
  Summable.of_norm_bounded (hw.mul_left ((4 : ℝ) ^ T))
    (norm_rootExponentialDerivativeTerm_le a hσ k hT hx)

theorem rootExponentialDerivativeSeries_continuousOn (a : RightOnePoint → ℂ)
    {σ : ℂ} (hσ : σ = Complex.I ∨ σ = -Complex.I) (k : ℕ)
    {T : ℝ} (hT : 0 ≤ T)
    (hw : Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ (T + k))) :
    ContinuousOn (rootExponentialDerivativeSeries a σ k) (Icc (-T) T) := by
  apply continuousOn_tsum _ (hw.mul_left ((4 : ℝ) ^ T))
    (fun z x hx => norm_rootExponentialDerivativeTerm_le a hσ k hT (abs_le.mpr hx) z)
  intro z
  exact (by unfold rootExponentialDerivativeTerm; fun_prop :
    Continuous (rootExponentialDerivativeTerm a σ k z)).continuousOn

theorem rootExponentialDerivativeSeries_hasDerivAt (a : RightOnePoint → ℂ)
    {σ : ℂ} (hσ : σ = Complex.I ∨ σ = -Complex.I) (k : ℕ)
    {T : ℝ} (hT : 0 < T)
    (hw₀ : Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ (T + k)))
    (hw₁ : Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ (T + (k + 1 : ℕ))))
    {x : ℝ} (hx : x ∈ Ioo (-T) T) :
    HasDerivAt (rootExponentialDerivativeSeries a σ k)
      (rootExponentialDerivativeSeries a σ (k + 1) x) x := by
  apply hasDerivAt_tsum_of_isPreconnected (hw₁.mul_left ((4 : ℝ) ^ T))
    isOpen_Ioo isPreconnected_Ioo
    (fun z y _ => rootExponentialDerivativeTerm_hasDerivAt a σ k z y)
    (fun z y hy => norm_rootExponentialDerivativeTerm_le a hσ (k + 1) hT.le
      (abs_le.mpr ⟨hy.1.le, hy.2.le⟩) z)
    (show (0 : ℝ) ∈ Ioo (-T) T by constructor <;> linarith)
    (rootExponentialDerivativeSeries_summable a hσ k hT.le hw₀ (by simpa using hT.le)) hx

/-- The finite-order intermediate theorem retains only explicit weighted
summability inputs, all of which are discharged for the actual coefficients. -/
theorem rootExponentialDerivativeSeries_contDiffOn (a : RightOnePoint → ℂ)
    {σ : ℂ} (hσ : σ = Complex.I ∨ σ = -Complex.I) {T : ℝ} (hT : 0 < T)
    (n k : ℕ)
    (hw : ∀ j : ℕ, j ≤ n →
      Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ (T + (k + j : ℕ)))) :
    ContDiffOn ℝ (n : ℕ∞ω) (rootExponentialDerivativeSeries a σ k) (Ioo (-T) T) := by
  induction n generalizing k with
  | zero =>
    apply contDiffOn_zero.mpr
    exact (rootExponentialDerivativeSeries_continuousOn a hσ k hT.le
      (by simpa only [Nat.add_zero] using hw 0 le_rfl)).mono Ioo_subset_Icc_self
  | succ n ih =>
    have hw₀ := hw 0 (Nat.zero_le _)
    have hw₁ := hw 1 (Nat.succ_le_succ (Nat.zero_le n))
    simp only [Nat.add_zero] at hw₀
    have hd (x : ℝ) (hx : x ∈ Ioo (-T) T) :=
      rootExponentialDerivativeSeries_hasDerivAt a hσ k hT hw₀ hw₁ hx
    have hnext : ContDiffOn ℝ (n : ℕ∞ω)
        (rootExponentialDerivativeSeries a σ (k + 1)) (Ioo (-T) T) := by
      apply ih (k + 1)
      intro j hj
      have hh := hw (j + 1) (Nat.succ_le_succ hj)
      have he : (k + 1) + j = k + (j + 1) := by omega
      rw [he]
      exact hh
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
    apply (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).mpr
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact hnext.congr (fun x hx => (hd x hx).deriv)

def rootCosineSeries (a : RightOnePoint → ℂ) (x : ℝ) : ℂ :=
  ∑' z : RightOnePoint, a z * Complex.cos ((z : ℂ) * (x : ℂ))

theorem rootCosineSeries_eq_exponential_average (a : RightOnePoint → ℂ)
    {T x : ℝ} (hT : 0 ≤ T)
    (hw : Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ T))
    (hx : |x| ≤ T) :
    rootCosineSeries a x =
      (rootExponentialDerivativeSeries a Complex.I 0 x +
        rootExponentialDerivativeSeries a (-Complex.I) 0 x) / 2 := by
  have hwp : Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ (T + (0 : ℕ))) := by
    simpa only [Nat.cast_zero, add_zero] using hw
  have hp := rootExponentialDerivativeSeries_summable a (Or.inl rfl) 0 hT hwp hx
  have hm := rootExponentialDerivativeSeries_summable a (Or.inr rfl) 0 hT hwp hx
  have he (z : RightOnePoint) : a z * Complex.cos ((z : ℂ) * (x : ℂ)) =
      (rootExponentialDerivativeTerm a Complex.I 0 z x +
        rootExponentialDerivativeTerm a (-Complex.I) 0 z x) / 2 := by
    have hh := Complex.two_cos ((z : ℂ) * (x : ℂ))
    have h₁ : ((z : ℂ) * (x : ℂ)) * Complex.I = Complex.I * (z : ℂ) * (x : ℂ) := by ring
    have h₂ : -((z : ℂ) * (x : ℂ)) * Complex.I = -Complex.I * (z : ℂ) * (x : ℂ) := by ring
    rw [h₁, h₂] at hh
    simp only [rootExponentialDerivativeTerm, pow_zero, mul_one]
    linear_combination (a z / 2) * hh
  unfold rootCosineSeries rootExponentialDerivativeSeries
  simp_rw [he]
  rw [tsum_div_const, hp.tsum_add hm]

theorem rootCosineSeries_contDiffOn (a : RightOnePoint → ℂ) {T : ℝ}
    (hT : 0 < T) (n : ℕ)
    (hw : ∀ j : ℕ, j ≤ n →
      Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ (T + j))) :
    ContDiffOn ℝ (n : ℕ∞ω) (rootCosineSeries a) (Ioo (-T) T) := by
  have hw' : ∀ j : ℕ, j ≤ n →
      Summable (fun z : RightOnePoint => ‖a z‖ * ‖(z : ℂ)‖ ^ (T + (0 + j : ℕ))) := by
    simpa only [Nat.zero_add] using hw
  have hp := rootExponentialDerivativeSeries_contDiffOn a (Or.inl rfl) hT n 0 hw'
  have hm := rootExponentialDerivativeSeries_contDiffOn a (Or.inr rfl) hT n 0 hw'
  apply (hp.add hm |>.div_const (2 : ℂ)).congr
  intro x hx
  exact rootCosineSeries_eq_exponential_average a hT.le
    (by simpa only [Nat.cast_zero, add_zero] using hw 0 (Nat.zero_le _))
    (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)

theorem besselResidueExponentialDerivativeSeries_contDiffOn (M n k : ℕ)
    {σ : ℂ} (hσ : σ = Complex.I ∨ σ = -Complex.I) {T : ℝ} (hT : 0 < T)
    (hMT : T + k + n < 2 * M - 1) :
    ContDiffOn ℝ (n : ℕ∞ω)
      (rootExponentialDerivativeSeries (fun z => besselResidueCoefficient M (z : ℂ)) σ k)
      (Ioo (-T) T) := by
  apply rootExponentialDerivativeSeries_contDiffOn _ hσ hT n k
  intro j hj
  have hjR : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hs := (besselResidueCoefficient_weight_summable M
    (b := T + (k + j : ℕ)) (by push_cast; linarith)).subtype
    (fun z : onePoints => 0 < (z : ℂ).re)
  exact hs

theorem besselCosineSeries_contDiffOn (M n : ℕ) {T : ℝ} (hT : 0 < T)
    (hMT : T + n < 2 * M - 1) :
    ContDiffOn ℝ (n : ℕ∞ω) (besselCosineSeries M) (Ioo (-T) T) := by
  apply rootCosineSeries_contDiffOn _ hT n
  intro j hj
  have hjR : (j : ℝ) ≤ n := by exact_mod_cast hj
  exact (besselResidueCoefficient_weight_summable M (b := T + j) (by linarith)).subtype
    (fun z : onePoints => 0 < (z : ℂ).re)

def scaledBesselResidueCoefficient (M : ℕ) (τ : ℝ) (z : ℂ) : ℂ :=
  besselResidueCoefficient M z / (J0 ((τ : ℂ) * z) - 1)

theorem scaledBesselResidueCoefficient_weight_summable (M : ℕ) {τ b : ℝ}
    (hτ : 1 < τ) (hb : b < 2 * M - 1) :
    Summable (fun z : onePoints => ‖scaledBesselResidueCoefficient M τ z‖ * ‖(z : ℂ)‖ ^ b) := by
  have hs := (besselResidueCoefficient_weight_summable M hb).mul_left (1 / scaledOnePointGap τ)
  apply Summable.of_nonneg_of_le
    (fun z => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)) _ hs
  intro z
  have hi : ‖J0 ((τ : ℂ) * (z : ℂ)) - 1‖⁻¹ ≤ 1 / scaledOnePointGap τ := by
    have hh := (scaled_one_point_inverse_defect_norm_lt hτ z.property.1 z.property.2).le
    rw [norm_inv] at hh
    rwa [norm_sub_rev]
  unfold scaledBesselResidueCoefficient
  rw [norm_div, div_eq_mul_inv]
  calc
    _ ≤ (‖besselResidueCoefficient M z‖ * (1 / scaledOnePointGap τ)) * ‖(z : ℂ)‖ ^ b :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hi (norm_nonneg _)) (Real.rpow_nonneg (norm_nonneg _) _)
    _ = _ := by ring

def scaledBesselCosineSeries (M : ℕ) (τ : ℝ) : ℝ → ℂ :=
  rootCosineSeries (fun z : RightOnePoint => scaledBesselResidueCoefficient M τ (z : ℂ))

theorem scaledBesselResidueExponentialDerivativeSeries_contDiffOn (M n k : ℕ)
    {τ : ℝ} (hτ : 1 < τ) {σ : ℂ} (hσ : σ = Complex.I ∨ σ = -Complex.I)
    {T : ℝ} (hT : 0 < T) (hMT : T + k + n < 2 * M - 1) :
    ContDiffOn ℝ (n : ℕ∞ω)
      (rootExponentialDerivativeSeries
        (fun z => scaledBesselResidueCoefficient M τ (z : ℂ)) σ k) (Ioo (-T) T) := by
  apply rootExponentialDerivativeSeries_contDiffOn _ hσ hT n k
  intro j hj
  have hjR : (j : ℝ) ≤ n := by exact_mod_cast hj
  exact (scaledBesselResidueCoefficient_weight_summable M hτ
    (b := T + (k + j : ℕ)) (by push_cast; linarith)).subtype
      (fun z : onePoints => 0 < (z : ℂ).re)

theorem scaledBesselCosineSeries_contDiffOn (M n : ℕ) {τ : ℝ} (hτ : 1 < τ)
    {T : ℝ} (hT : 0 < T) (hMT : T + n < 2 * M - 1) :
    ContDiffOn ℝ (n : ℕ∞ω) (scaledBesselCosineSeries M τ) (Ioo (-T) T) := by
  apply rootCosineSeries_contDiffOn _ hT n
  intro j hj
  have hjR : (j : ℝ) ≤ n := by exact_mod_cast hj
  exact (scaledBesselResidueCoefficient_weight_summable M hτ
    (b := T + j) (by linarith)).subtype (fun z : onePoints => 0 < (z : ℂ).re)

end J0RadialUniqueness
