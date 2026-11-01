import Mathlib.Analysis.Complex.PhragmenLindelof

/-! An unweighted order-one Phragmén--Lindelöf tool for a rotated quadrant.

The boundary bounds and the actual order-one estimate remain explicit inputs
of this general analytic lemma. This is not the local two-radius theorem, nor
does it assert those estimates for the paper's spectral quotient.
-/

noncomputable section

open Set Filter Bornology Asymptotics Complex
open scoped Topology

namespace J0RadialUniqueness

/-- A genuine order-one growth estimate outside a unit disk is enough for the
unweighted PL bound on a unit rotation of the closed first quadrant. The proof
uses exponent c=1, strictly below the quadrant's critical exponent two. -/
theorem rotatedQuadrantPL_order_one
    (q : ℂ → ℂ) (hq : Differentiable ℂ q) (a : ℂ) (_ha : ‖a‖ = 1)
    {C A B : ℝ} (_hA : 0 < A) (_hB : 0 ≤ B)
    (hre : ∀ t : ℝ, 0 ≤ t → ‖q (a * (t : ℂ))‖ ≤ C)
    (him : ∀ t : ℝ, 0 ≤ t → ‖q (a * ((t : ℂ) * Complex.I))‖ ≤ C)
    (hgrowth : ∀ w : ℂ, 0 < w.re → 0 < w.im → 1 ≤ ‖w‖ →
      ‖q (a * w)‖ ≤ A * Real.exp (B * ‖w‖)) :
    ∀ w : ℂ, 0 ≤ w.re → 0 ≤ w.im → ‖q (a * w)‖ ≤ C := by
  let f : ℂ → ℂ := fun w => q (a * w)
  have hf : Differentiable ℂ f :=
    hq.comp ((differentiable_const (c := a)).mul differentiable_id)
  have hd : DiffContOnCl ℂ f (Ioi (0 : ℝ) ×ℂ Ioi (0 : ℝ)) := hf.diffContOnCl
  have hO : ∃ c < (2 : ℝ), ∃ D : ℝ,
      f =O[cobounded ℂ ⊓ 𝓟 (Ioi (0 : ℝ) ×ℂ Ioi (0 : ℝ))]
        fun w : ℂ => Real.exp (D * ‖w‖ ^ c) := by
    refine ⟨1, by norm_num, B, ?_⟩
    apply Asymptotics.IsBigO.of_bound A
    rw [eventually_inf_principal]
    filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with w hw hquad
    have hwre : 0 < w.re := hquad.1
    have hwim : 0 < w.im := hquad.2
    simpa only [f, Real.rpow_one, Real.norm_eq_abs, Real.abs_exp] using
      hgrowth w hwre hwim hw
  intro w hwre hwim
  exact PhragmenLindelof.quadrant_I (f := f) (z := w) hd hO hre him hwre hwim

end J0RadialUniqueness
