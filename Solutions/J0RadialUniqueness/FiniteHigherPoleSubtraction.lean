import Solutions.J0RadialUniqueness.FiniteSimplePoleSubtraction

/-! Finite Laurent principal parts at a pole of any prescribed order.
Repeated genuine divided differences give the analytic remainder and exact
Taylor coefficients; no formal Taylor or residue expansion is assumed. -/

noncomputable section
open scoped Topology

namespace J0RadialUniqueness

def iteratedDSlope (f : ℂ → ℂ) (a : ℂ) : ℕ → ℂ → ℂ
  | 0 => f
  | n + 1 => dslope (iteratedDSlope f a n) a

@[simp] theorem iteratedDSlope_zero (f : ℂ → ℂ) (a : ℂ) : iteratedDSlope f a 0 = f := rfl

theorem iteratedDSlope_analyticAt {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (n : ℕ) : AnalyticAt ℂ (iteratedDSlope f a n) a := by
  induction n with
  | zero => exact hf
  | succ n ih => exact analyticAt_dslope_base ih

theorem iteratedDSlope_taylor_identity (f : ℂ → ℂ) (a z : ℂ) (n : ℕ) :
    f z = (∑ k ∈ Finset.range n, (z - a) ^ k * iteratedDSlope f a k a) +
      (z - a) ^ n * iteratedDSlope f a n z := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs : (z - a) * iteratedDSlope f a (n + 1) z =
          iteratedDSlope f a n z - iteratedDSlope f a n a := by
        simpa only [iteratedDSlope, smul_eq_mul] using sub_smul_dslope (iteratedDSlope f a n) a z
      rw [Finset.sum_range_succ, pow_succ]
      linear_combination ih - (z - a) ^ n * hs

def finiteLaurentPrincipalPart (f : ℂ → ℂ) (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, iteratedDSlope f a k a / (z - a) ^ (n - k)

theorem div_pow_eq_finiteLaurentPrincipalPart_add (f : ℂ → ℂ) (a : ℂ) (n : ℕ)
    {z : ℂ} (hz : z ≠ a) :
    f z / (z - a) ^ n = finiteLaurentPrincipalPart f a n z + iteratedDSlope f a n z := by
  have hn : (z - a) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hz)
  rw [iteratedDSlope_taylor_identity f a z n, add_div, mul_div_cancel_left₀ _ hn]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := (Finset.mem_range.mp hk).le
  have hp : (z - a) ^ n = (z - a) ^ k * (z - a) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [hp]
  field_simp [sub_ne_zero.mpr hz]

/-- The actual higher-pole subtraction has an analytic extension, with the
extension specified explicitly rather than supplied as an assumption. -/
theorem exists_analytic_higher_pole_remainder {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (n : ℕ) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
      ∀ z : ℂ, z ≠ a → f z / (z - a) ^ n = finiteLaurentPrincipalPart f a n z + h z :=
  ⟨iteratedDSlope f a n, iteratedDSlope_analyticAt hf n,
    fun _ hz => div_pow_eq_finiteLaurentPrincipalPart_add f a n hz⟩

end J0RadialUniqueness
