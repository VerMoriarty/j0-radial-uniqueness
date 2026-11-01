import Solutions.J0RadialUniqueness.K0SeriesODE

/-! The quadratic pullback and principal-logarithm product rules identify the
exact modified Bessel differential equation of the independent K₀ series. -/

noncomputable section

open scoped Topology

namespace J0RadialUniqueness

def quadraticSlope (f : ℂ → ℂ) (z : ℂ) : ℂ := (z / 2) * deriv f (z ^ 2 / 4)

def quadraticAccel (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * deriv f (z ^ 2 / 4) +
    (z ^ 2 / 4) * deriv (deriv f) (z ^ 2 / 4)

theorem quadraticArg_hasDerivAt (z : ℂ) :
    HasDerivAt (fun w : ℂ => w ^ 2 / 4) (z / 2) z := by
  have h := ((hasDerivAt_id z).pow 2).div_const (4 : ℂ)
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply]
  ring

theorem quadraticPullback_hasDerivAt {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (z : ℂ) :
    HasDerivAt (fun w : ℂ => f (w ^ 2 / 4)) (quadraticSlope f z) z := by
  have h : HasDerivAt (fun w : ℂ => f (w ^ 2 / 4))
      (deriv f (z ^ 2 / 4) * (z / 2)) z := by
    simpa only [Function.comp_def, id_eq] using
      (hf (z ^ 2 / 4)).hasDerivAt.comp z (quadraticArg_hasDerivAt z)
  apply h.congr_deriv
  dsimp only [quadraticSlope]
  ring

theorem quadraticSlope_hasDerivAt {f : ℂ → ℂ}
    (hf' : Differentiable ℂ (deriv f)) (z : ℂ) :
    HasDerivAt (quadraticSlope f) (quadraticAccel f z) z := by
  have hcomp : HasDerivAt (fun w : ℂ => deriv f (w ^ 2 / 4))
      (deriv (deriv f) (z ^ 2 / 4) * (z / 2)) z := by
    simpa only [Function.comp_def, id_eq] using
      (hf' (z ^ 2 / 4)).hasDerivAt.comp z (quadraticArg_hasDerivAt z)
  have h := ((hasDerivAt_id z).div_const (2 : ℂ)).mul hcomp
  apply h.congr_deriv
  dsimp only [quadraticAccel]
  simp only [id_eq, Pi.pow_apply]
  ring

theorem modifiedI0_hasDerivAt (z : ℂ) :
    HasDerivAt modifiedI0 (quadraticSlope F z) z :=
  quadraticPullback_hasDerivAt F_differentiable z

@[simp] theorem modifiedI0_deriv (z : ℂ) : deriv modifiedI0 z = quadraticSlope F z :=
  (modifiedI0_hasDerivAt z).deriv

theorem modifiedI0_deriv_hasDerivAt (z : ℂ) :
    HasDerivAt (deriv modifiedI0) (quadraticAccel F z) z := by
  have hfun : deriv modifiedI0 = quadraticSlope F := by
    funext w
    exact modifiedI0_deriv w
  rw [hfun]
  exact quadraticSlope_hasDerivAt F_deriv_differentiable z

@[simp] theorem modifiedI0_secondDerivative (z : ℂ) :
    deriv (deriv modifiedI0) z = quadraticAccel F z :=
  (modifiedI0_deriv_hasDerivAt z).deriv

theorem K0Correction_hasDerivAt (z : ℂ) :
    HasDerivAt K0Correction (quadraticSlope harmonicF z) z :=
  quadraticPullback_hasDerivAt harmonicF_differentiable z

@[simp] theorem K0Correction_deriv (z : ℂ) :
    deriv K0Correction z = quadraticSlope harmonicF z :=
  (K0Correction_hasDerivAt z).deriv

theorem K0Correction_deriv_hasDerivAt (z : ℂ) :
    HasDerivAt (deriv K0Correction) (quadraticAccel harmonicF z) z := by
  have hfun : deriv K0Correction = quadraticSlope harmonicF := by
    funext w
    exact K0Correction_deriv w
  rw [hfun]
  exact quadraticSlope_hasDerivAt harmonicF_deriv_differentiable z

@[simp] theorem K0Correction_secondDerivative (z : ℂ) :
    deriv (deriv K0Correction) z = quadraticAccel harmonicF z :=
  (K0Correction_deriv_hasDerivAt z).deriv

def modifiedBesselOperator (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z ^ 2 * deriv (deriv f) z + z * deriv f z - z ^ 2 * f z

theorem modifiedI0_ode (z : ℂ) : modifiedBesselOperator modifiedI0 z = 0 := by
  rw [modifiedBesselOperator, modifiedI0_secondDerivative, modifiedI0_deriv]
  dsimp only [quadraticAccel, quadraticSlope, modifiedI0]
  linear_combination z ^ 2 * (F_ode (z ^ 2 / 4))

theorem K0Correction_ode (z : ℂ) :
    modifiedBesselOperator K0Correction z = 2 * z * deriv modifiedI0 z := by
  rw [modifiedBesselOperator, K0Correction_secondDerivative, K0Correction_deriv,
    modifiedI0_deriv]
  dsimp only [quadraticAccel, quadraticSlope, K0Correction]
  linear_combination z ^ 2 * (harmonicF_ode (z ^ 2 / 4))

def K0LogFactor (z : ℂ) : ℂ :=
  Complex.log (z / 2) + (Real.eulerMascheroniConstant : ℂ)

def K0SeriesSlope (z : ℂ) : ℂ :=
  -z⁻¹ * modifiedI0 z - K0LogFactor z * deriv modifiedI0 z + deriv K0Correction z

def K0SeriesAccel (z : ℂ) : ℂ :=
  (z ^ 2)⁻¹ * modifiedI0 z - (2 / z) * deriv modifiedI0 z -
    K0LogFactor z * deriv (deriv modifiedI0) z + deriv (deriv K0Correction) z

theorem K0LogFactor_hasDerivAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt K0LogFactor z⁻¹ z := by
  have hz0 := Complex.slitPlane_ne_zero hz
  have hlog : HasDerivAt (fun w : ℂ => Complex.log (w / 2))
      ((z / 2)⁻¹ * (1 / 2)) z := by
    simpa only [Function.comp_def, id_eq] using
      (Complex.hasDerivAt_log (slitPlane_div_two hz)).comp z
        ((hasDerivAt_id z).div_const (2 : ℂ))
  have h := hlog.add_const (Real.eulerMascheroniConstant : ℂ)
  change HasDerivAt K0LogFactor ((z / 2)⁻¹ * (1 / 2)) z at h
  apply h.congr_deriv
  field_simp [hz0] <;> ring

theorem K0Series_hasDerivAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt K0Series (K0SeriesSlope z) z := by
  have hA := (modifiedI0_analyticAt z).differentiableAt.hasDerivAt
  have hB := (K0Correction_analyticAt z).differentiableAt.hasDerivAt
  have h := ((K0LogFactor_hasDerivAt hz).neg.mul hA).add hB
  have hfun : -K0LogFactor * modifiedI0 + K0Correction = K0Series := by
    funext w
    rfl
  rw [hfun] at h
  apply h.congr_deriv
  dsimp only [K0SeriesSlope]
  simp only [Pi.neg_apply]
  ring

theorem K0Series_deriv {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    deriv K0Series z = K0SeriesSlope z :=
  (K0Series_hasDerivAt hz).deriv

theorem K0SeriesSlope_hasDerivAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt K0SeriesSlope (K0SeriesAccel z) z := by
  have hz0 := Complex.slitPlane_ne_zero hz
  have hA := (modifiedI0_analyticAt z).differentiableAt.hasDerivAt
  have hA' := (modifiedI0_deriv_hasDerivAt z).differentiableAt.hasDerivAt
  have hB' := (K0Correction_deriv_hasDerivAt z).differentiableAt.hasDerivAt
  have h := (((hasDerivAt_inv hz0).neg.mul hA).sub
    ((K0LogFactor_hasDerivAt hz).mul hA')).add hB'
  have hfun : ((-(fun w : ℂ => w⁻¹)) * modifiedI0 -
      K0LogFactor * deriv modifiedI0) + deriv K0Correction = K0SeriesSlope := by
    funext w
    rfl
  rw [hfun] at h
  apply h.congr_deriv
  dsimp only [K0SeriesAccel]
  simp only [Pi.neg_apply]
  field_simp [hz0] <;> ring

theorem K0Series_deriv_hasDerivAt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (deriv K0Series) (K0SeriesAccel z) z := by
  have heq : deriv K0Series =ᶠ[𝓝 z] K0SeriesSlope := by
    filter_upwards [Complex.isOpen_slitPlane.eventually_mem hz] with w hw
    exact K0Series_deriv hw
  exact (K0SeriesSlope_hasDerivAt hz).congr_of_eventuallyEq heq

theorem K0Series_secondDerivative {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    deriv (deriv K0Series) z = K0SeriesAccel z :=
  (K0Series_deriv_hasDerivAt hz).deriv

theorem K0Series_operator_identity {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    modifiedBesselOperator K0Series z = modifiedBesselOperator K0Correction z -
      K0LogFactor z * modifiedBesselOperator modifiedI0 z - 2 * z * deriv modifiedI0 z := by
  have hz0 := Complex.slitPlane_ne_zero hz
  have hvalue : K0Series z = -K0LogFactor z * modifiedI0 z + K0Correction z := rfl
  unfold modifiedBesselOperator
  rw [K0Series_secondDerivative hz, K0Series_deriv hz, hvalue]
  dsimp only [K0SeriesAccel, K0SeriesSlope]
  field_simp [hz0] <;> ring

/-- The actual independent principal-branch series solves the order-zero modified Bessel ODE. -/
theorem K0Series_ode {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    modifiedBesselOperator K0Series z = 0 := by
  rw [K0Series_operator_identity hz, K0Correction_ode, modifiedI0_ode]
  ring

end J0RadialUniqueness
