import Solutions.J0RadialUniqueness.SimpleZeroDivision
import Mathlib.Tactic

/-! Subtraction of finitely many actual simple principal parts. The values at
the removed poles are explicit divided-difference derivatives. This provides
an analytic remainder for subsequent contour arguments, without a residue or
removability hypothesis hidden in the interface. -/

noncomputable section
open Filter Set
open scoped Topology Classical

namespace J0RadialUniqueness

def simplePoleResidue (f g : ℂ → ℂ) (a : ℂ) : ℂ := f a / deriv g a

def simplePoleRegularPart (f g : ℂ → ℂ) (a z : ℂ) : ℂ :=
  dslope (fun w => f w / dslope g a w) a z

theorem simplePoleRegularPart_analyticAt {f g : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) (hd : deriv g a ≠ 0) :
    AnalyticAt ℂ (simplePoleRegularPart f g a) a := by
  apply analyticAt_dslope_base
  exact hf.div (analyticAt_dslope_base hg) (by simpa only [dslope_same] using hd)

theorem simplePoleRegularPart_eventuallyEq {f g : ℂ → ℂ} {a : ℂ}
    (hg : AnalyticAt ℂ g a) (hga : g a = 0) (hd : deriv g a ≠ 0) :
    ∀ᶠ z : ℂ in 𝓝 a, z ≠ a →
      simplePoleRegularPart f g a z = f z / g z - simplePoleResidue f g a / (z - a) := by
  have hne : ∀ᶠ z in 𝓝 a, dslope g a z ≠ 0 :=
    (analyticAt_dslope_base hg).continuousAt.eventually_ne
      (by simpa only [dslope_same] using hd)
  filter_upwards [hne] with z hz hza
  have hfac : (z - a) * dslope g a z = g z := by
    simpa only [smul_eq_mul] using sub_smul_dslope_of_zero hga z
  have hgz : g z ≠ 0 := by rw [← hfac]; exact mul_ne_zero (sub_ne_zero.mpr hza) hz
  unfold simplePoleRegularPart simplePoleResidue
  rw [dslope_of_ne _ hza]
  simp only [slope_def_field, dslope_same]
  rw [← hfac]
  field_simp [sub_ne_zero.mpr hza, hz, hd]

def finiteSimplePoleRemainder (S : Finset ℂ) (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z ∈ S then
    simplePoleRegularPart f g z z - ∑ b ∈ S.erase z, simplePoleResidue f g b / (z - b)
  else f z / g z - ∑ b ∈ S, simplePoleResidue f g b / (z - b)

theorem finiteSimplePoleRemainder_eq_of_notMem (S : Finset ℂ) (f g : ℂ → ℂ)
    {z : ℂ} (hz : z ∉ S) :
    finiteSimplePoleRemainder S f g z =
      f z / g z - ∑ b ∈ S, simplePoleResidue f g b / (z - b) := by
  simp only [finiteSimplePoleRemainder, if_neg hz]

theorem finiteSimplePoleRemainder_eventuallyEq_at_pole
    (S : Finset ℂ) {f g : ℂ → ℂ} {a : ℂ} (ha : a ∈ S)
    (hg : AnalyticAt ℂ g a) (hga : g a = 0) (hd : deriv g a ≠ 0) :
    finiteSimplePoleRemainder S f g =ᶠ[𝓝 a] fun z =>
      simplePoleRegularPart f g a z - ∑ b ∈ S.erase a, simplePoleResidue f g b / (z - b) := by
  have havoid : ∀ᶠ z : ℂ in 𝓝 a, ∀ b ∈ S.erase a, z ≠ b := by
    rw [eventually_all_finset]
    intro b hb
    exact eventually_ne_nhds (Finset.ne_of_mem_erase hb).symm
  filter_upwards [havoid, simplePoleRegularPart_eventuallyEq hg hga hd] with z hz heq
  by_cases hza : z = a
  · subst z
    simp only [finiteSimplePoleRemainder, if_pos ha]
  · have hzS : z ∉ S := by
      intro hzS
      exact hz z (Finset.mem_erase.mpr ⟨hza, hzS⟩) rfl
    rw [finiteSimplePoleRemainder_eq_of_notMem S f g hzS, heq hza]
    have hsum := Finset.sum_erase_add S
      (fun b => simplePoleResidue f g b / (z - b)) ha
    rw [← hsum]
    ring

theorem finiteSimplePoleRemainder_analyticAt_pole
    (S : Finset ℂ) {f g : ℂ → ℂ} {a : ℂ} (ha : a ∈ S)
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hga : g a = 0) (hd : deriv g a ≠ 0) :
    AnalyticAt ℂ (finiteSimplePoleRemainder S f g) a := by
  have hsum : AnalyticAt ℂ (fun z =>
      ∑ b ∈ S.erase a, simplePoleResidue f g b / (z - b)) a := by
    apply Finset.analyticAt_fun_sum
    intro b hb
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm)
  exact ((simplePoleRegularPart_analyticAt hf hg hd).sub hsum).congr
    (finiteSimplePoleRemainder_eventuallyEq_at_pole S ha hg hga hd).symm

theorem finiteSimplePoleRemainder_analyticAt_nonpole
    (S : Finset ℂ) {f g : ℂ → ℂ} {a : ℂ} (ha : a ∉ S)
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) (hga : g a ≠ 0) :
    AnalyticAt ℂ (finiteSimplePoleRemainder S f g) a := by
  have hsum : AnalyticAt ℂ (fun z => ∑ b ∈ S, simplePoleResidue f g b / (z - b)) a := by
    apply Finset.analyticAt_fun_sum
    intro b hb
    exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (by intro hab; exact ha (hab ▸ hb)))
  apply ((hf.div hg hga).sub hsum).congr
  have hnear : ∀ᶠ z : ℂ in 𝓝 a, z ∉ S :=
    (S.finite_toSet.isClosed.isOpen_compl.mem_nhds ha)
  filter_upwards [hnear] with z hz
  exact (finiteSimplePoleRemainder_eq_of_notMem S f g hz).symm

/-- Every actual zero in the domain is explicitly included in the finite set.
Only genuine analyticity and simplicity of those zeros are required. -/
theorem finiteSimplePoleRemainder_analyticOnNhd (S : Finset ℂ)
    {f g : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U)
    (hroots : ∀ a ∈ S, g a = 0)
    (hsimple : ∀ a ∈ S, deriv g a ≠ 0)
    (hcomplete : ∀ a ∈ U, g a = 0 → a ∈ S) :
    AnalyticOnNhd ℂ (finiteSimplePoleRemainder S f g) U := by
  intro a haU
  by_cases ha : a ∈ S
  · exact finiteSimplePoleRemainder_analyticAt_pole S ha (hf a haU) (hg a haU)
      (hroots a ha) (hsimple a ha)
  · exact finiteSimplePoleRemainder_analyticAt_nonpole S ha (hf a haU) (hg a haU)
      (fun hz => ha (hcomplete a haU hz))

end J0RadialUniqueness
