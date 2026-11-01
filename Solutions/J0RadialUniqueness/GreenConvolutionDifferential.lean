import Solutions.J0RadialUniqueness.LocalFilterPoleElimination

/-! Differentiating the actual compact Green convolution. In particular, local
vanishing of both u and its Green convolution gives a zero circular mean on
the same open center domain, without assuming a global mean identity. -/

noncomputable section

open MeasureTheory Laplacian Filter
open scoped ContDiff Topology

namespace J0RadialUniqueness

theorem laplacian_localConvolution_planarGreen {u : Plane → ℂ}
    (hu : ContDiff ℝ ∞ u) {r : ℝ} (hr : 0 < r) (x : Plane) :
    laplacian (localConvolution (planarGreenKernel r) u) x = circularMean u r x - u x := by
  have he : complexConvolution (fun y : Plane => (planarGreenKernel r y : ℂ)) u =
      localConvolution (planarGreenKernel r) u := funext (complexConvolution_cast_planarGreen r u)
  have hc : HasCompactSupport (fun y : Plane => (planarGreenKernel r y : ℂ)) :=
    (planarGreenKernel_hasCompactSupport r).comp_left (g := Complex.ofReal) rfl
  calc
    _ = laplacian (complexConvolution (fun y : Plane => (planarGreenKernel r y : ℂ)) u) x :=
      congrArg (fun f : Plane → ℂ => laplacian f x) he.symm
    _ = complexConvolution (fun y : Plane => (planarGreenKernel r y : ℂ)) (laplacian u) x := by
      convert! laplacian_complexConvolution (k := fun y : Plane => (planarGreenKernel r y : ℂ))
        (planarGreenKernel_integrable hr).ofReal hc hu x using 1
    _ = localConvolution (planarGreenKernel r) (laplacian u) x :=
      complexConvolution_cast_planarGreen r (laplacian u) x
    _ = _ := localConvolution_planarGreen_laplacian hu x hr

theorem circularMean_eq_zero_of_green_and_value_zero {u : Plane → ℂ}
    (hu : ContDiff ℝ ∞ u) {r : ℝ} (hr : 0 < r) {U : Set Plane} (hU : IsOpen U)
    (hG : ∀ x ∈ U, localConvolution (planarGreenKernel r) u x = 0)
    (hz : ∀ x ∈ U, u x = 0) : ∀ x ∈ U, circularMean u r x = 0 := by
  intro x hx
  have heq : localConvolution (planarGreenKernel r) u =ᶠ[𝓝 x] (fun _ : Plane => (0 : ℂ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hG y hy
  have hΔ : laplacian (localConvolution (planarGreenKernel r) u) x = 0 := by
    simpa using (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds
  have hh := laplacian_localConvolution_planarGreen hu hr x
  rw [hΔ, hz x hx, sub_zero] at hh
  exact hh.symm

end J0RadialUniqueness
