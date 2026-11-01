import Solutions.J0RadialUniqueness.FiniteHigherPoleSubtraction

/-! Gluing finitely many specified local principal-part subtractions into a
single genuine analytic remainder. This permits a higher-order origin pole
and simple nonzero spectral poles in the same contour argument. -/

noncomputable section
open Filter Set
open scoped Topology Classical

namespace J0RadialUniqueness

def finitePrincipalRemainder (S : Finset ℂ) (F : ℂ → ℂ) (P H : ℂ → ℂ → ℂ)
    (z : ℂ) : ℂ :=
  if z ∈ S then H z z - ∑ b ∈ S.erase z, P b z
  else F z - ∑ b ∈ S, P b z

theorem finitePrincipalRemainder_eq_of_notMem (S : Finset ℂ) (F : ℂ → ℂ)
    (P H : ℂ → ℂ → ℂ) {z : ℂ} (hz : z ∉ S) :
    finitePrincipalRemainder S F P H z = F z - ∑ b ∈ S, P b z := by
  simp only [finitePrincipalRemainder, if_neg hz]

theorem finitePrincipalRemainder_eventuallyEq_at_pole (S : Finset ℂ)
    (F : ℂ → ℂ) (P H : ℂ → ℂ → ℂ) {a : ℂ} (ha : a ∈ S)
    (hlocal : ∀ᶠ z : ℂ in 𝓝 a, z ≠ a → F z = P a z + H a z) :
    finitePrincipalRemainder S F P H =ᶠ[𝓝 a]
      fun z => H a z - ∑ b ∈ S.erase a, P b z := by
  have havoid : ∀ᶠ z : ℂ in 𝓝 a, ∀ b ∈ S.erase a, z ≠ b := by
    rw [eventually_all_finset]
    intro b hb
    exact eventually_ne_nhds (Finset.ne_of_mem_erase hb).symm
  filter_upwards [havoid, hlocal] with z hz heq
  by_cases hza : z = a
  · subst z
    simp only [finitePrincipalRemainder, if_pos ha]
  · have hzS : z ∉ S := by
      intro hzS
      exact hz z (Finset.mem_erase.mpr ⟨hza, hzS⟩) rfl
    rw [finitePrincipalRemainder_eq_of_notMem S F P H hzS, heq hza]
    rw [← Finset.sum_erase_add S (fun b => P b z) ha]
    ring

theorem finitePrincipalRemainder_analyticAt_pole (S : Finset ℂ)
    (F : ℂ → ℂ) (P H : ℂ → ℂ → ℂ) {a : ℂ} (ha : a ∈ S)
    (hH : AnalyticAt ℂ (H a) a)
    (hP : ∀ b ∈ S.erase a, AnalyticAt ℂ (P b) a)
    (hlocal : ∀ᶠ z : ℂ in 𝓝 a, z ≠ a → F z = P a z + H a z) :
    AnalyticAt ℂ (finitePrincipalRemainder S F P H) a := by
  exact (hH.sub (Finset.analyticAt_fun_sum _ hP)).congr
    (finitePrincipalRemainder_eventuallyEq_at_pole S F P H ha hlocal).symm

theorem finitePrincipalRemainder_analyticAt_nonpole (S : Finset ℂ)
    (F : ℂ → ℂ) (P H : ℂ → ℂ → ℂ) {a : ℂ} (ha : a ∉ S)
    (hF : AnalyticAt ℂ F a) (hP : ∀ b ∈ S, AnalyticAt ℂ (P b) a) :
    AnalyticAt ℂ (finitePrincipalRemainder S F P H) a := by
  apply (hF.sub (Finset.analyticAt_fun_sum _ hP)).congr
  have hnear : ∀ᶠ z : ℂ in 𝓝 a, z ∉ S :=
    S.finite_toSet.isClosed.isOpen_compl.mem_nhds ha
  filter_upwards [hnear] with z hz
  exact (finitePrincipalRemainder_eq_of_notMem S F P H hz).symm

/-- Each local decomposition is an eventual equality on the actual punctured
neighborhood. The conclusion is an analytic function on the whole requested
domain, including every pole and all their explicitly filled values. -/
theorem finitePrincipalRemainder_analyticOnNhd (S : Finset ℂ)
    (F : ℂ → ℂ) (P H : ℂ → ℂ → ℂ) {U : Set ℂ}
    (hF : ∀ a ∈ U, a ∉ S → AnalyticAt ℂ F a)
    (hP : ∀ a ∈ U, ∀ b ∈ S, a ≠ b → AnalyticAt ℂ (P b) a)
    (hH : ∀ a ∈ U, a ∈ S → AnalyticAt ℂ (H a) a)
    (hlocal : ∀ a ∈ U, a ∈ S →
      ∀ᶠ z : ℂ in 𝓝 a, z ≠ a → F z = P a z + H a z) :
    AnalyticOnNhd ℂ (finitePrincipalRemainder S F P H) U := by
  intro a haU
  by_cases ha : a ∈ S
  · exact finitePrincipalRemainder_analyticAt_pole S F P H ha (hH a haU ha)
      (fun b hb => hP a haU b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm)
      (hlocal a haU ha)
  · exact finitePrincipalRemainder_analyticAt_nonpole S F P H ha (hF a haU ha)
      (fun b hb => hP a haU b hb (by intro hab; exact ha (hab ▸ hb)))

end J0RadialUniqueness
