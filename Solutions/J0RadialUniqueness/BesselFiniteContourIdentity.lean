import Solutions.J0RadialUniqueness.BesselSpectralBoxSums
import Solutions.J0RadialUniqueness.FinitePrincipalContourIdentity
import Solutions.J0RadialUniqueness.SquareContourPrimitive
import Mathlib.Tactic

/-! The actual finite spectral residue identity. All local analytic principal
parts and every pole in the box are provided by the Bessel modules. The contour
identity is the proved finite-principal-part Cauchy--Goursat theorem. -/

noncomputable section

open Set Filter
open scoped Topology Classical

namespace J0RadialUniqueness

def besselSpectralPrincipalPart (M : ℕ) (t b z : ℂ) : ℂ :=
  if b = 0 then besselSpectralOriginPrincipalPart M t z
    else besselSpectralSimpleResidue M t b / (z - b)

def besselSpectralRegularPart (M : ℕ) (t b z : ℂ) : ℂ :=
  if b = 0 then besselSpectralOriginRegularPart M t z
    else besselSpectralSimpleRegularPart M t b z

theorem besselSpectralPrincipalPart_zero (M : ℕ) (t : ℂ) :
    besselSpectralPrincipalPart M t 0 = besselSpectralOriginPrincipalPart M t := by
  funext z
  exact if_pos rfl

theorem besselSpectralPrincipalPart_ne_zero (M : ℕ) (t : ℂ) {b : ℂ} (hb : b ≠ 0) :
    besselSpectralPrincipalPart M t b =
      (fun z => besselSpectralSimpleResidue M t b / (z - b)) := by
  funext z
  exact if_neg hb

theorem besselSpectralRegularPart_zero (M : ℕ) (t : ℂ) :
    besselSpectralRegularPart M t 0 = besselSpectralOriginRegularPart M t := by
  funext z
  exact if_pos rfl

theorem besselSpectralRegularPart_ne_zero (M : ℕ) (t : ℂ) {b : ℂ} (hb : b ≠ 0) :
    besselSpectralRegularPart M t b = besselSpectralSimpleRegularPart M t b := by
  funext z
  exact if_neg hb

theorem besselSpectralPrincipalPart_analyticAt (M : ℕ) (t b : ℂ) {z : ℂ} (hzb : z ≠ b) :
    AnalyticAt ℂ (besselSpectralPrincipalPart M t b) z := by
  by_cases hb : b = 0
  · subst b
    rw [besselSpectralPrincipalPart_zero]
    unfold besselSpectralOriginPrincipalPart finiteLaurentPrincipalPart
    apply analyticAt_const.mul
    apply Finset.analyticAt_fun_sum
    intro k hk
    exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
      (pow_ne_zero _ (sub_ne_zero.mpr hzb))
  · rw [besselSpectralPrincipalPart_ne_zero M t hb]
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzb)

theorem besselSpectralRegularPart_analyticAt (M : ℕ) (t : ℂ) {b : ℂ}
    (hpole : b = 0 ∨ J0 b = 1) : AnalyticAt ℂ (besselSpectralRegularPart M t b) b := by
  by_cases hb : b = 0
  · subst b
    rw [besselSpectralRegularPart_zero]
    exact besselSpectralOriginRegularPart_analyticAt M t
  · rw [besselSpectralRegularPart_ne_zero M t hb]
    exact besselSpectralSimpleRegularPart_analyticAt M t hb (hpole.resolve_left hb)

theorem besselSpectralPrincipalPart_local_identity (M : ℕ) (t : ℂ) {b : ℂ}
    (hpole : b = 0 ∨ J0 b = 1) :
    ∀ᶠ z : ℂ in 𝓝 b, z ≠ b → besselSpectralIntegrand M t z =
      besselSpectralPrincipalPart M t b z + besselSpectralRegularPart M t b z := by
  by_cases hb : b = 0
  · subst b
    exact Eventually.of_forall (fun z hz => by
      simpa only [besselSpectralPrincipalPart, besselSpectralRegularPart, if_pos rfl, ite_true] using
        besselSpectralIntegrand_eq_origin_principal_add M t hz)
  · simpa only [besselSpectralPrincipalPart, besselSpectralRegularPart, if_neg hb] using
      besselSpectralSimpleRegularPart_eventuallyEq M t hb (hpole.resolve_left hb)

theorem besselSpectralOriginPrincipalPart_integral {a : ℝ} (ha : 0 < a) (M : ℕ) (t : ℂ) :
    squareBoundaryIntegral a (besselSpectralOriginPrincipalPart M t) =
      (2 * (Real.pi : ℂ) * Complex.I) * besselSpectralOriginResidue M t := by
  unfold besselSpectralOriginPrincipalPart
  rw [squareBoundaryIntegral_const_mul,
    squareBoundaryIntegral_finiteLaurentPrincipalPart ha _ _ (by
      unfold besselSpectralOriginOrder
      omega)]
  unfold besselSpectralOriginResidue
  ring

theorem besselSpectralSimplePrincipalPart_integral {a : ℝ} (ha : 0 < a) (M : ℕ) (t b : ℂ)
    (hb : b ≠ 0) (hbre : |b.re| < a) (hbim : |b.im| < a) :
    squareBoundaryIntegral a (besselSpectralPrincipalPart M t b) =
      (2 * (Real.pi : ℂ) * Complex.I) * besselSpectralSimpleResidue M t b := by
  rw [besselSpectralPrincipalPart_ne_zero M t hb]
  change squareBoundaryIntegral a
    (fun z => besselSpectralSimpleResidue M t b * (z - b)⁻¹) = _
  rw [squareBoundaryIntegral_const_mul, squareBoundaryIntegral_inv_sub ha hbre hbim]
  ring

theorem besselSpectralClosedBox_eq_square (n : ℕ) :
    besselSpectralClosedBox n = closedSpectralSquare (besselSpectralBoxRadius n) := by
  ext z
  simp only [besselSpectralClosedBox, closedSpectralSquare, mem_setOf_eq,
    Complex.mem_reProdIm, mem_Icc, ← abs_le]

/-- Finite contour formula with the actual origin polynomial and the actual
right-half-plane finite root sum. No residue or spectral expansion theorem is
an input. -/
theorem besselSpectral_finite_contour_identity (M : ℕ) (t : ℂ) {n : ℕ} (hn : 100 ≤ n) :
    squareBoundaryIntegral (besselSpectralBoxRadius n) (besselSpectralIntegrand M t) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ((besselPolePolynomial M).eval t - besselSpectralRightBoxSum M t n) := by
  let S : Finset ℂ := besselSpectralBoxPoleFinset n
  let a : ℝ := besselSpectralBoxRadius n
  have ha : 0 < a := besselSpectralBoxRadius_pos n
  have hS (b : ℂ) (hb : b ∈ S) : |b.re| < a ∧ |b.im| < a :=
    besselSpectralBoxPoles_subset_open hn ((mem_besselSpectralBoxPoleFinset n b).mp hb)
  have hF (z : ℂ) (hz : z ∈ closedSpectralSquare a) (hzS : z ∉ S) :
      AnalyticAt ℂ (besselSpectralIntegrand M t) z := by
    have hzbox : z ∈ besselSpectralClosedBox n := by
      rw [besselSpectralClosedBox_eq_square]
      exact hz
    have hz0 : z ≠ 0 := fun hz0 => hzS ((mem_besselSpectralBoxPoleFinset n z).mpr
      ⟨hzbox, Or.inl hz0⟩)
    have hJ : J0 z ≠ 1 := fun hJ => hzS ((mem_besselSpectralBoxPoleFinset n z).mpr
      ⟨hzbox, Or.inr hJ⟩)
    exact besselSpectralIntegrand_analyticAt M t hz0 hJ
  have hformula := squareBoundaryIntegral_eq_sum_principalParts ha S
    (besselSpectralIntegrand M t) (besselSpectralPrincipalPart M t) (besselSpectralRegularPart M t)
    hS hF (fun z _ b _ hzb => besselSpectralPrincipalPart_analyticAt M t b hzb)
    (fun b _ hb => besselSpectralRegularPart_analyticAt M t
      ((mem_besselSpectralBoxPoleFinset n b).mp hb).2)
    (fun b _ hb => besselSpectralPrincipalPart_local_identity M t
      ((mem_besselSpectralBoxPoleFinset n b).mp hb).2)
  have hzero : (0 : ℂ) ∈ S :=
    (mem_besselSpectralBoxPoleFinset n 0).mpr (besselSpectralBoxPoles_zero n)
  have hnonzero (b : ℂ) (hb : b ∈ S.erase 0) :
      squareBoundaryIntegral a (besselSpectralPrincipalPart M t b) =
        (2 * (Real.pi : ℂ) * Complex.I) * besselSpectralSimpleResidue M t b :=
    besselSpectralSimplePrincipalPart_integral ha M t b (Finset.mem_erase.mp hb).1
      (hS b (Finset.mem_of_mem_erase hb)).1 (hS b (Finset.mem_of_mem_erase hb)).2
  have horigin : squareBoundaryIntegral a (besselSpectralPrincipalPart M t 0) =
      (2 * (Real.pi : ℂ) * Complex.I) * besselSpectralOriginResidue M t := by
    rw [besselSpectralPrincipalPart_zero]
    exact besselSpectralOriginPrincipalPart_integral ha M t
  calc
    _ = ∑ b ∈ S, squareBoundaryIntegral a (besselSpectralPrincipalPart M t b) := hformula
    _ = (∑ b ∈ S.erase 0, squareBoundaryIntegral a (besselSpectralPrincipalPart M t b)) +
        squareBoundaryIntegral a (besselSpectralPrincipalPart M t 0) :=
      (Finset.sum_erase_add S _ hzero).symm
    _ = (∑ b ∈ S.erase 0, (2 * (Real.pi : ℂ) * Complex.I) * besselSpectralSimpleResidue M t b) +
        (2 * (Real.pi : ℂ) * Complex.I) * besselSpectralOriginResidue M t := by
      rw [horigin]
      congr 1
      exact Finset.sum_congr rfl hnonzero
    _ = (2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ b ∈ S.erase 0, besselSpectralSimpleResidue M t b) + besselSpectralOriginResidue M t) := by
      rw [← Finset.mul_sum]
      ring
    _ = _ := by
      change (2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ b ∈ (besselSpectralBoxPoleFinset n).erase 0, besselSpectralSimpleResidue M t b) +
          besselSpectralOriginResidue M t) = _
      rw [besselSpectralBox_nonzero_residue_sum, besselSpectralOriginResidue_eq_polynomial]
      ring

end J0RadialUniqueness
