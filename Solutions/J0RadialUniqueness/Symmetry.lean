import Solutions.J0RadialUniqueness.Series

noncomputable section

namespace J0RadialUniqueness

def quadrantRep (z : ℂ) : ℂ := ⟨|z.re|, |z.im|⟩

theorem quadrantRep_orbit (z : ℂ) :
    quadrantRep z = z ∨ quadrantRep z = -z ∨
      quadrantRep z = starRingEnd ℂ z ∨ quadrantRep z = -starRingEnd ℂ z := by
  by_cases hx : 0 ≤ z.re <;> by_cases hy : 0 ≤ z.im
  · left
    apply Complex.ext <;> simp [quadrantRep, abs_of_nonneg hx, abs_of_nonneg hy]
  · right; right; left
    apply Complex.ext <;> simp [quadrantRep, abs_of_nonneg hx, abs_of_neg (lt_of_not_ge hy)]
  · right; right; right
    apply Complex.ext <;> simp [quadrantRep, abs_of_neg (lt_of_not_ge hx), abs_of_nonneg hy]
  · right; left
    apply Complex.ext <;> simp [quadrantRep, abs_of_neg (lt_of_not_ge hx), abs_of_neg (lt_of_not_ge hy)]

theorem norm_J0_quadrantRep (z : ℂ) : ‖J0 (quadrantRep z)‖ = ‖J0 z‖ := by
  rcases quadrantRep_orbit z with h | h | h | h
  · rw [h]
  · rw [h, J0_neg]
  · rw [h, J0_conj, RCLike.norm_conj]
  · rw [h, J0_neg, J0_conj, RCLike.norm_conj]

theorem J0_quadrantRep (z : ℂ) (hz : J0 z = 1) : J0 (quadrantRep z) = 1 := by
  rcases quadrantRep_orbit z with h | h | h | h
  · rw [h, hz]
  · rw [h, J0_neg, hz]
  · rw [h, J0_conj, hz, map_one]
  · rw [h, J0_neg, J0_conj, hz, map_one]

theorem quadrantRep_pos_mul (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    quadrantRep ((c : ℂ) * z) = (c : ℂ) * quadrantRep z := by
  apply Complex.ext <;> simp [quadrantRep, abs_mul, abs_of_nonneg hc]

theorem norm_J0_mul_quadrantRep (c : ℝ) (hc : 0 ≤ c) (z : ℂ) :
    ‖J0 ((c : ℂ) * quadrantRep z)‖ = ‖J0 ((c : ℂ) * z)‖ := by
  rw [← quadrantRep_pos_mul c hc z, norm_J0_quadrantRep]

theorem quadrantRep_in_principalSector (z : ℂ) (hreal : 0 < (z ^ 2).re)
    (him : z.im ≠ 0) : PrincipalSector (quadrantRep z) := by
  constructor
  · exact abs_pos.mpr him
  · change |z.im| < |z.re|
    apply (sq_lt_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    simp only [sq_abs]
    rw [pow_two, Complex.mul_re] at hreal
    nlinarith

end J0RadialUniqueness
