import Solutions.J0RadialUniqueness.BesselBiorthogonality

/-! The actual cosine spectral modes used in the geometric construction.
Both the circle multiplier and the Laplacian eigen-equation are proved from
the already verified exponential formulas, for every complex frequency. -/

noncomputable section
open Laplacian
open scoped ContDiff

namespace J0RadialUniqueness

def spectralCosine (nu : ℂ) (x : Plane) : ℂ := Complex.cos (nu * (x 0 : ℂ))

theorem spectralCosine_eq_exponential_combination (nu : ℂ) :
    spectralCosine nu = fun x => (1 / 2 : ℂ) *
      (spectralExponential (Complex.I * nu) x + spectralExponential (-Complex.I * nu) x) := by
  funext x
  unfold spectralCosine spectralExponential Complex.cos
  have hp : nu * (x 0 : ℂ) * Complex.I = (Complex.I * nu) * (x 0 : ℂ) := by ring
  have hm : -(nu * (x 0 : ℂ)) * Complex.I = (-Complex.I * nu) * (x 0 : ℂ) := by ring
  rw [hp, hm]
  ring

@[fun_prop] theorem spectralCosine_contDiff (nu : ℂ) : ContDiff ℝ ∞ (spectralCosine nu) := by
  rw [spectralCosine_eq_exponential_combination]
  exact contDiff_const.mul ((spectralExponential_contDiff _).add (spectralExponential_contDiff _))

theorem circularMean_spectralCosine (nu : ℂ) (r : ℝ) (x : Plane) :
    circularMean (spectralCosine nu) r x = spectralCosine nu x * J0 ((r : ℂ) * nu) := by
  have hplus : J0 (Complex.I * (Complex.I * nu) * (r : ℂ)) = J0 ((r : ℂ) * nu) := by
    have he : Complex.I * (Complex.I * nu) * (r : ℂ) =
        Complex.I ^ 2 * ((r : ℂ) * nu) := by ring
    rw [he, Complex.I_sq, neg_one_mul, J0_neg]
  have hminus : J0 (Complex.I * (-Complex.I * nu) * (r : ℂ)) = J0 ((r : ℂ) * nu) := by
    have he : Complex.I * (-Complex.I * nu) * (r : ℂ) =
        -(Complex.I ^ 2) * ((r : ℂ) * nu) := by ring
    rw [he, Complex.I_sq]
    simp
  have heq : (fun y => spectralExponential (Complex.I * nu) y +
      spectralExponential (-Complex.I * nu) y) =
      fun y => spectralExponential (Complex.I * nu) y +
        (1 : ℂ) * spectralExponential (-Complex.I * nu) y := by funext y; rw [one_mul]
  rw [spectralCosine_eq_exponential_combination, circularMean_complex_mul_const,
    heq, circularMean_add_const_mul_of_continuous (spectralExponential_contDiff _).continuous
      (spectralExponential_contDiff _).continuous,
    circularMean_spectralExponential, circularMean_spectralExponential, hplus, hminus]
  simp only [one_mul]
  ring

theorem laplacian_spectralCosine (nu : ℂ) (x : Plane) :
    laplacian (spectralCosine nu) x = -nu ^ 2 * spectralCosine nu x := by
  have h₁ : ContDiff ℝ 2 (spectralExponential (Complex.I * nu)) :=
    (contDiff_infty.mp (spectralExponential_contDiff _)) 2
  have h₂ : ContDiff ℝ 2 (spectralExponential (-Complex.I * nu)) :=
    (contDiff_infty.mp (spectralExponential_contDiff _)) 2
  have heq : spectralCosine nu = (1 / 2 : ℂ) •
      (spectralExponential (Complex.I * nu) + spectralExponential (-Complex.I * nu)) := by
    funext y
    rw [spectralCosine_eq_exponential_combination]
    rfl
  have hadd : ContDiffAt ℝ 2
      (spectralExponential (Complex.I * nu) + spectralExponential (-Complex.I * nu)) x := by
    convert! (h₁.add h₂).contDiffAt using 1 <;> rfl
  have hs := InnerProductSpace.laplacian_smul (1 / 2 : ℂ) hadd
  have ha : laplacian (spectralExponential (Complex.I * nu) +
      spectralExponential (-Complex.I * nu)) x =
      laplacian (spectralExponential (Complex.I * nu)) x +
        laplacian (spectralExponential (-Complex.I * nu)) x := by
    convert! h₁.contDiffAt.laplacian_add h₂.contDiffAt using 1 <;> rfl
  rw [heq, hs, ha]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, laplacian_spectralExponential]
  have hp : (Complex.I * nu) ^ 2 = -nu ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
  have hm : (-Complex.I * nu) ^ 2 = -nu ^ 2 := by rw [mul_pow, neg_sq, Complex.I_sq]; ring
  rw [hp, hm]
  ring

@[simp] theorem spectralCosine_zero (nu : ℂ) : spectralCosine nu (0 : Plane) = 1 := by
  simp [spectralCosine]

end J0RadialUniqueness
