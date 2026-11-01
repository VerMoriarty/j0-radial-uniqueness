import Solutions.J0RadialUniqueness.SquareContourIntegral

/-! Algebra of the actual four interval integrals defining a square contour.
Integrability is recorded for each edge, including when the function has poles
in the interior. This avoids applying global continuity to a meromorphic
integrand or silently distributing a Bochner integral over non-L1 summands. -/

noncomputable section
open MeasureTheory Set
open scoped Topology Interval

namespace J0RadialUniqueness

structure SquareBoundaryIntegrable (a : ℝ) (f : ℂ → ℂ) : Prop where
  bottom : IntervalIntegrable (fun t : ℝ => f ((t : ℂ) - (a : ℂ) * Complex.I)) volume (-a) a
  top : IntervalIntegrable (fun t : ℝ => f ((t : ℂ) + (a : ℂ) * Complex.I)) volume (-a) a
  right : IntervalIntegrable (fun t : ℝ => f ((a : ℂ) + (t : ℂ) * Complex.I)) volume (-a) a
  left : IntervalIntegrable (fun t : ℝ => f (-(a : ℂ) + (t : ℂ) * Complex.I)) volume (-a) a

theorem squareBoundary_edge_mem {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : t ∈ uIcc (-a) a) :
    ((t : ℂ) - (a : ℂ) * Complex.I) ∈ squareBoundarySet a ∧
    ((t : ℂ) + (a : ℂ) * Complex.I) ∈ squareBoundarySet a ∧
    ((a : ℂ) + (t : ℂ) * Complex.I) ∈ squareBoundarySet a ∧
    (-(a : ℂ) + (t : ℂ) * Complex.I) ∈ squareBoundarySet a := by
  rw [uIcc_of_le (by linarith : -a ≤ a)] at ht
  have hta : |t| ≤ a := abs_le.mpr ht
  simp only [squareBoundarySet, mem_setOf_eq, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, mul_zero, mul_one, zero_mul, zero_sub,
    sub_zero, add_zero, zero_add, neg_zero, abs_neg, abs_of_nonneg ha]
  exact ⟨Or.inr ⟨True.intro, hta⟩, Or.inr ⟨True.intro, hta⟩,
    Or.inl ⟨True.intro, hta⟩, Or.inl ⟨True.intro, hta⟩⟩

theorem squareBoundaryIntegrable_of_continuousOn {a : ℝ} (ha : 0 ≤ a)
    {f : ℂ → ℂ} (hf : ContinuousOn f (squareBoundarySet a)) : SquareBoundaryIntegrable a f := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hf.comp (by fun_prop) (fun _ ht => (squareBoundary_edge_mem ha ht).1)).intervalIntegrable
  · exact (hf.comp (by fun_prop) (fun _ ht => (squareBoundary_edge_mem ha ht).2.1)).intervalIntegrable
  · exact (hf.comp (by fun_prop) (fun _ ht => (squareBoundary_edge_mem ha ht).2.2.1)).intervalIntegrable
  · exact (hf.comp (by fun_prop) (fun _ ht => (squareBoundary_edge_mem ha ht).2.2.2)).intervalIntegrable

theorem squareBoundaryIntegral_congr {a : ℝ} (ha : 0 ≤ a) {f g : ℂ → ℂ}
    (hfg : EqOn f g (squareBoundarySet a)) : squareBoundaryIntegral a f = squareBoundaryIntegral a g := by
  have h₀ : (∫ t : ℝ in -a..a, f ((t : ℂ) - (a : ℂ) * Complex.I)) =
      ∫ t : ℝ in -a..a, g ((t : ℂ) - (a : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr fun _ ht => hfg (squareBoundary_edge_mem ha ht).1
  have h₁ : (∫ t : ℝ in -a..a, f ((t : ℂ) + (a : ℂ) * Complex.I)) =
      ∫ t : ℝ in -a..a, g ((t : ℂ) + (a : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr fun _ ht => hfg (squareBoundary_edge_mem ha ht).2.1
  have h₂ : (∫ t : ℝ in -a..a, f ((a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ in -a..a, g ((a : ℂ) + (t : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr fun _ ht => hfg (squareBoundary_edge_mem ha ht).2.2.1
  have h₃ : (∫ t : ℝ in -a..a, f (-(a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ in -a..a, g (-(a : ℂ) + (t : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr fun _ ht => hfg (squareBoundary_edge_mem ha ht).2.2.2
  unfold squareBoundaryIntegral
  rw [h₀, h₁, h₂, h₃]

theorem SquareBoundaryIntegrable.add {a : ℝ} {f g : ℂ → ℂ}
    (hf : SquareBoundaryIntegrable a f) (hg : SquareBoundaryIntegrable a g) :
    SquareBoundaryIntegrable a (fun z => f z + g z) :=
  ⟨hf.bottom.add hg.bottom, hf.top.add hg.top, hf.right.add hg.right, hf.left.add hg.left⟩

theorem SquareBoundaryIntegrable.sub {a : ℝ} {f g : ℂ → ℂ}
    (hf : SquareBoundaryIntegrable a f) (hg : SquareBoundaryIntegrable a g) :
    SquareBoundaryIntegrable a (fun z => f z - g z) :=
  ⟨hf.bottom.sub hg.bottom, hf.top.sub hg.top, hf.right.sub hg.right, hf.left.sub hg.left⟩

theorem squareBoundaryIntegral_add {a : ℝ} {f g : ℂ → ℂ}
    (hf : SquareBoundaryIntegrable a f) (hg : SquareBoundaryIntegrable a g) :
    squareBoundaryIntegral a (fun z => f z + g z) =
      squareBoundaryIntegral a f + squareBoundaryIntegral a g := by
  simp only [squareBoundaryIntegral, intervalIntegral.integral_add hf.bottom hg.bottom,
    intervalIntegral.integral_add hf.top hg.top, intervalIntegral.integral_add hf.right hg.right,
    intervalIntegral.integral_add hf.left hg.left]
  ring

theorem squareBoundaryIntegral_sub {a : ℝ} {f g : ℂ → ℂ}
    (hf : SquareBoundaryIntegrable a f) (hg : SquareBoundaryIntegrable a g) :
    squareBoundaryIntegral a (fun z => f z - g z) =
      squareBoundaryIntegral a f - squareBoundaryIntegral a g := by
  simp only [squareBoundaryIntegral, intervalIntegral.integral_sub hf.bottom hg.bottom,
    intervalIntegral.integral_sub hf.top hg.top, intervalIntegral.integral_sub hf.right hg.right,
    intervalIntegral.integral_sub hf.left hg.left]
  ring

theorem squareBoundaryIntegral_const_mul (a : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    squareBoundaryIntegral a (fun z => c * f z) = c * squareBoundaryIntegral a f := by
  simp only [squareBoundaryIntegral, intervalIntegral.integral_const_mul]
  ring

theorem squareBoundaryIntegral_sum {ι : Type*} (S : Finset ι) {a : ℝ} (f : ι → ℂ → ℂ)
    (hf : ∀ b ∈ S, SquareBoundaryIntegrable a (f b)) :
    squareBoundaryIntegral a (fun z => ∑ b ∈ S, f b z) = ∑ b ∈ S, squareBoundaryIntegral a (f b) := by
  unfold squareBoundaryIntegral
  rw [intervalIntegral.integral_finset_sum (fun b hb => (hf b hb).bottom),
    intervalIntegral.integral_finset_sum (fun b hb => (hf b hb).top),
    intervalIntegral.integral_finset_sum (fun b hb => (hf b hb).right),
    intervalIntegral.integral_finset_sum (fun b hb => (hf b hb).left)]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

end J0RadialUniqueness
