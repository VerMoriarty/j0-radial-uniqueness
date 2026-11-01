import Solutions.J0RadialUniqueness.DistributionLaplacian

noncomputable section
open MeasureTheory Set Laplacian
open scoped ContDiff

namespace J0RadialUniqueness

theorem laplacian_test_eq_zero_outside (U : TopologicalSpace.Opens Plane)
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) {x : Plane} (hx : x ∉ (U : Set Plane)) :
    laplacian (φ : Plane → ℝ) x = 0 := by
  rw [← testLaplacianCLM_apply U φ x]
  by_contra hn
  exact hx ((testLaplacianCLM U φ).tsupport_subset
    ((subset_tsupport (testLaplacianCLM U φ)) hn))

theorem laplacian_test_pairing_congr_ae (U : TopologicalSpace.Opens Plane)
    {f g : Plane → ℂ} (hfg : f =ᵐ[volume.restrict (U : Set Plane)] g)
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    (∫ x : Plane, (laplacian (φ : Plane → ℝ) x : ℂ) * f x) =
      ∫ x : Plane, (laplacian (φ : Plane → ℝ) x : ℂ) * g x := by
  have h : ∀ᵐ x : Plane, x ∈ (U : Set Plane) → f x = g x :=
    (ae_restrict_iff' U.isOpen.measurableSet).mp hfg
  apply integral_congr_ae
  filter_upwards [h] with x hx
  by_cases hxu : x ∈ (U : Set Plane)
  · rw [hx hxu]
  · rw [laplacian_test_eq_zero_outside U φ hxu]
    simp only [Complex.ofReal_zero, zero_mul]

/-- The weak Laplace equation depends only on the local AE class, without any
pointwise representative assumption at exceptional points. -/
theorem distributionHarmonicOn_congr_ae (U : TopologicalSpace.Opens Plane)
    {f g : Plane → ℂ} (hfg : f =ᵐ[volume.restrict (U : Set Plane)] g) :
    DistributionHarmonicOn f (U : Set Plane) ↔ DistributionHarmonicOn g (U : Set Plane) := by
  have transport {a b : Plane → ℂ} (hab : a =ᵐ[volume.restrict (U : Set Plane)] b)
      (ha : DistributionHarmonicOn a (U : Set Plane)) :
      DistributionHarmonicOn b (U : Set Plane) := by
    intro φ hφ hcompact hsupport
    let ψ : TestFunction U ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hcompact, hsupport⟩
    have heq := laplacian_test_pairing_congr_ae U hab ψ
    exact heq.symm.trans (ha φ hφ hcompact hsupport)
  exact ⟨transport hfg, transport hfg.symm⟩

end J0RadialUniqueness
