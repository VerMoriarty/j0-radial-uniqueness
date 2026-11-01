import Solutions.J0RadialUniqueness.MollifiedWeakHarmonic
import Mathlib.Analysis.Distribution.Distribution

/-! The concrete distribution represented by a locally integrable function and
its actual second distributional derivatives. Test functions have order
`⊤ : ℕ∞`, namely smooth order, rather than analytic order in `ℕ∞ω`.
-/

noncomputable section

open MeasureTheory Laplacian
open scoped ContDiff Topology

namespace J0RadialUniqueness

/-- The regular distribution represented by `f`. Mathlib makes this zero when
`f` is not locally integrable on `U`; every evaluation theorem below supplies
the required local integrability hypothesis explicitly. -/
def regularDistribution (U : TopologicalSpace.Opens Plane) (f : Plane → ℂ) :
    Distribution U ℂ (⊤ : ℕ∞) :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) volume f

theorem regularDistribution_apply (U : TopologicalSpace.Opens Plane) {f : Plane → ℂ}
    (hf : LocallyIntegrableOn f (U : Set Plane)) (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    regularDistribution U f φ = ∫ x : Plane, (φ x : ℂ) * f x := by
  change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ)
    volume f φ = _
  rw [TestFunction.integralAgainstBilinCLM_eq_integral hf]
  rfl

def distributionAxis0 : Plane := (EuclideanSpace.basisFun (Fin 2) ℝ) 0
def distributionAxis1 : Plane := (EuclideanSpace.basisFun (Fin 2) ℝ) 1

/-- Directional differentiation on the genuine LF space of smooth tests. -/
def testDirectionalCLM (U : TopologicalSpace.Opens Plane) (v : Plane) :
    TestFunction U ℝ (⊤ : ℕ∞) →L[ℝ] TestFunction U ℝ (⊤ : ℕ∞) :=
  TestFunction.lineDerivCLM ℝ v

theorem testDirectionalCLM_apply (U : TopologicalSpace.Opens Plane)
    (v x : Plane) (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    testDirectionalCLM U v φ x = directionalKernel (φ : Plane → ℝ) v x := by
  change TestFunction.fderivCLM ℝ (⊤ : ℕ∞) (⊤ : ℕ∞) φ x v = _
  rw [TestFunction.fderivCLM_apply_of_le φ (by simp)]
  rfl

theorem testDirectionalCLM_coe (U : TopologicalSpace.Opens Plane)
    (v : Plane) (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    (testDirectionalCLM U v φ : Plane → ℝ) = directionalKernel (φ : Plane → ℝ) v := by
  funext x
  exact testDirectionalCLM_apply U v x φ

/-- The Laplace operator on compactly supported smooth tests is a continuous
linear map for the actual LF topology, since its two derivatives are. -/
def testLaplacianCLM (U : TopologicalSpace.Opens Plane) :
    TestFunction U ℝ (⊤ : ℕ∞) →L[ℝ] TestFunction U ℝ (⊤ : ℕ∞) :=
  (testDirectionalCLM U distributionAxis0).comp (testDirectionalCLM U distributionAxis0) +
    (testDirectionalCLM U distributionAxis1).comp (testDirectionalCLM U distributionAxis1)

theorem real_laplacian_eq_distributionAxes (φ : Plane → ℝ) (x : Plane) :
    laplacian φ x =
      fderiv ℝ (fderiv ℝ φ) x distributionAxis0 distributionAxis0 +
        fderiv ℝ (fderiv ℝ φ) x distributionAxis1 distributionAxis1 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [Fin.sum_univ_two, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, distributionAxis0, distributionAxis1]

/-- Evaluation of the LF operator is the actual Fréchet-derivative Laplacian. -/
theorem testLaplacianCLM_apply (U : TopologicalSpace.Opens Plane)
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) (x : Plane) :
    testLaplacianCLM U φ x = laplacian (φ : Plane → ℝ) x := by
  have hφ : ContDiff ℝ ∞ (φ : Plane → ℝ) := φ.contDiff
  have h0 := testDirectionalCLM_apply U distributionAxis0 x
    (testDirectionalCLM U distributionAxis0 φ)
  have h1 := testDirectionalCLM_apply U distributionAxis1 x
    (testDirectionalCLM U distributionAxis1 φ)
  rw [testDirectionalCLM_coe U distributionAxis0 φ] at h0
  rw [testDirectionalCLM_coe U distributionAxis1 φ] at h1
  change testDirectionalCLM U distributionAxis0 (testDirectionalCLM U distributionAxis0 φ) x +
    testDirectionalCLM U distributionAxis1 (testDirectionalCLM U distributionAxis1 φ) x = _
  rw [h0, h1]
  change directionalSecond (φ : Plane → ℝ) distributionAxis0 distributionAxis0 x +
    directionalSecond (φ : Plane → ℝ) distributionAxis1 distributionAxis1 x = _
  rw [directionalSecond_eq_fderiv hφ, directionalSecond_eq_fderiv hφ,
    real_laplacian_eq_distributionAxes]

/-- The weak Laplacian of the regular distribution, evaluated by transposing the
test Laplacian. Two differentiations account for the positive sign. -/
def weakLaplacianDistribution (U : TopologicalSpace.Opens Plane) (f : Plane → ℂ) :
    Distribution U ℂ (⊤ : ℕ∞) :=
  (regularDistribution U f).comp (testLaplacianCLM U)

/-- This is exactly the sum of the two genuine iterated distributional
directional derivatives supplied by Mathlib. -/
theorem weakLaplacianDistribution_eq_second_derivatives
    (U : TopologicalSpace.Opens Plane) (f : Plane → ℂ) :
    weakLaplacianDistribution U f =
      Distribution.lineDerivCLM (n := (⊤ : ℕ∞)) (k := (⊤ : ℕ∞)) distributionAxis0
        (Distribution.lineDerivCLM (n := (⊤ : ℕ∞)) (k := (⊤ : ℕ∞))
          distributionAxis0 (regularDistribution U f)) +
      Distribution.lineDerivCLM (n := (⊤ : ℕ∞)) (k := (⊤ : ℕ∞)) distributionAxis1
        (Distribution.lineDerivCLM (n := (⊤ : ℕ∞)) (k := (⊤ : ℕ∞))
          distributionAxis1 (regularDistribution U f)) := by
  ext φ
  simp only [weakLaplacianDistribution, ContinuousLinearMap.comp_apply, testLaplacianCLM,
    ContinuousLinearMap.add_apply, map_add, Distribution.lineDerivCLM_apply,
    map_neg, neg_neg, testDirectionalCLM]
  change (regularDistribution U f)
      (testDirectionalCLM U distributionAxis0 (testDirectionalCLM U distributionAxis0 φ) +
        testDirectionalCLM U distributionAxis1 (testDirectionalCLM U distributionAxis1 φ)) =
    (regularDistribution U f)
        (testDirectionalCLM U distributionAxis0 (testDirectionalCLM U distributionAxis0 φ)) +
      (regularDistribution U f)
        (testDirectionalCLM U distributionAxis1 (testDirectionalCLM U distributionAxis1 φ))
  exact map_add (regularDistribution U f) _ _

theorem weakLaplacianDistribution_apply (U : TopologicalSpace.Opens Plane) {f : Plane → ℂ}
    (hf : LocallyIntegrableOn f (U : Set Plane)) (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    weakLaplacianDistribution U f φ =
      ∫ x : Plane, (laplacian (φ : Plane → ℝ) x : ℂ) * f x := by
  change (regularDistribution U f) (testLaplacianCLM U φ) = _
  rw [regularDistribution_apply U hf]
  simp only [testLaplacianCLM_apply]

/-- The integral giving the distributional Laplacian is genuinely integrable,
by compact support of the differentiated test and local integrability of `f`. -/
theorem weakLaplacianDistribution_integrable (U : TopologicalSpace.Opens Plane)
    {f : Plane → ℂ} (hf : LocallyIntegrableOn f (U : Set Plane))
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    Integrable (fun x : Plane => (laplacian (φ : Plane → ℝ) x : ℂ) * f x) := by
  have hi := TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
    hf (testLaplacianCLM U φ)
  simpa only [testLaplacianCLM_apply, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul] using hi

/-- The paper's raw-test formulation is equivalent to vanishing of the actual
Mathlib distributional Laplacian. The reverse direction bundles each raw test,
with its stated smoothness and support conditions, into the genuine LF space. -/
theorem distributionHarmonicOn_iff_weakLaplacianDistribution_eq_zero
    (U : TopologicalSpace.Opens Plane) {f : Plane → ℂ}
    (hf : LocallyIntegrableOn f (U : Set Plane)) :
    DistributionHarmonicOn f (U : Set Plane) ↔ weakLaplacianDistribution U f = 0 := by
  constructor
  · intro hweak
    ext φ
    rw [weakLaplacianDistribution_apply U hf]
    exact hweak (φ : Plane → ℝ) φ.contDiff φ.hasCompactSupport φ.tsupport_subset
  · intro hzero φ hφ hcompact hsupport
    let ψ : TestFunction U ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hcompact, hsupport⟩
    have htest : weakLaplacianDistribution U f ψ = 0 := by rw [hzero]; rfl
    rw [weakLaplacianDistribution_apply U hf] at htest
    exact htest

/-- Full auxiliary specification of the raw-test/native-distribution semantic
bridge. The open domain, original function and its exact local integrability
hypothesis are all quantified here. -/
def DistributionLaplacianBridgeStatement : Prop :=
  ∀ (U : TopologicalSpace.Opens Plane) (f : Plane → ℂ),
    LocallyIntegrableOn f (U : Set Plane) →
      (DistributionHarmonicOn f (U : Set Plane) ↔ weakLaplacianDistribution U f = 0)

theorem paper_distribution_laplacian_bridge : DistributionLaplacianBridgeStatement := by
  intro U f hf
  exact distributionHarmonicOn_iff_weakLaplacianDistribution_eq_zero U hf

end J0RadialUniqueness
