import Solutions.J0RadialUniqueness.LaplaceAnalytic
import Mathlib.Tactic

noncomputable section

namespace J0RadialUniqueness

theorem negI_mul_mem_slitPlane {z : ℂ} (hz : 0 < z.re) :
    -Complex.I * z ∈ Complex.slitPlane := by
  right
  simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, neg_zero, zero_mul, neg_mul, one_mul, zero_add]
  exact neg_ne_zero.mpr hz.ne'

theorem I_mul_mem_slitPlane {z : ℂ} (hz : 0 < z.re) :
    Complex.I * z ∈ Complex.slitPlane := by
  right
  simpa using hz.ne'

theorem rotated_laplace_base_plus (z : ℂ) (t : ℝ) :
    1 + (t : ℂ) / (2 * (-Complex.I * z)) =
      1 + Complex.I * (t : ℂ) / (2 * z) := by
  by_cases hz : z = 0
  · simp [hz]
  · field_simp [hz]
    ring_nf
    simp [Complex.I_sq, sub_eq_add_neg]

theorem rotated_laplace_base_minus (z : ℂ) (t : ℝ) :
    1 + (t : ℂ) / (2 * (Complex.I * z)) =
      1 - Complex.I * (t : ℂ) / (2 * z) := by
  by_cases hz : z = 0
  · simp [hz]
  · field_simp [hz]
    ring_nf
    simp [Complex.I_sq]

theorem APlus_eq_laplaceI (z : ℂ) : APlus z = laplaceI (-Complex.I * z) := by
  unfold APlus laplaceI
  congr 1
  funext t
  unfold plusKernel laplaceKernel
  rw [rotated_laplace_base_plus]

theorem AMinus_eq_laplaceI (z : ℂ) : AMinus z = laplaceI (Complex.I * z) := by
  unfold AMinus laplaceI
  congr 1
  funext t
  unfold minusKernel laplaceKernel
  rw [rotated_laplace_base_minus]

theorem rotated_moment_plus (z : ℂ) :
    laplaceMomentKernel (-Complex.I * z) = plusMomentKernel z := by
  funext t
  unfold laplaceMomentKernel plusMomentKernel
  rw [rotated_laplace_base_plus]

theorem rotated_moment_minus (z : ℂ) :
    laplaceMomentKernel (Complex.I * z) = minusMomentKernel z := by
  funext t
  unfold laplaceMomentKernel minusMomentKernel
  rw [rotated_laplace_base_minus]

theorem APlus_hasDerivAt {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt APlus
      (Complex.I / (4 * z ^ 2) * weightedIntegral (plusMomentKernel z)) z := by
  have hd := (laplaceI_hasDerivAt (negI_mul_mem_slitPlane hz)).comp z
    ((hasDerivAt_id z).const_mul (-Complex.I))
  have he : (laplaceI ∘ HMul.hMul (-Complex.I)) = APlus := by
    funext w
    exact (APlus_eq_laplaceI w).symm
  rw [he] at hd
  apply hd.congr_deriv
  rw [rotated_moment_plus]
  simp only [mul_one, mul_pow, neg_sq, Complex.I_sq]
  ring

theorem AMinus_hasDerivAt {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt AMinus
      (-Complex.I / (4 * z ^ 2) * weightedIntegral (minusMomentKernel z)) z := by
  have hd := (laplaceI_hasDerivAt (I_mul_mem_slitPlane hz)).comp z
    ((hasDerivAt_id z).const_mul Complex.I)
  have he : (laplaceI ∘ HMul.hMul Complex.I) = AMinus := by
    funext w
    exact (AMinus_eq_laplaceI w).symm
  rw [he] at hd
  apply hd.congr_deriv
  rw [rotated_moment_minus]
  simp only [mul_one, mul_pow, Complex.I_sq]
  ring

/-- The complete holomorphy and derivative part of Proposition 3.2, now unconditional. -/
theorem amplitude_derivatives : AmplitudeDerivativeStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact (APlus_hasDerivAt hz).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (AMinus_hasDerivAt hz).differentiableAt.differentiableWithinAt
  · intro z hz
    exact ⟨APlus_hasDerivAt hz, AMinus_hasDerivAt hz⟩

theorem amplitude_integrability : AmplitudeIntegrabilityStatement := by
  intro z hz
  have hp := laplace_integrability (-Complex.I * z) (negI_mul_mem_slitPlane hz)
  have hm := laplace_integrability (Complex.I * z) (I_mul_mem_slitPlane hz)
  have hpk : laplaceKernel (-Complex.I * z) = plusKernel z := by
    funext t
    unfold laplaceKernel plusKernel
    rw [rotated_laplace_base_plus]
  have hmk : laplaceKernel (Complex.I * z) = minusKernel z := by
    funext t
    unfold laplaceKernel minusKernel
    rw [rotated_laplace_base_minus]
  rw [hpk, rotated_moment_plus] at hp
  rw [hmk, rotated_moment_minus] at hm
  exact ⟨hp.1, hm.1, hp.2, hm.2⟩

end J0RadialUniqueness
