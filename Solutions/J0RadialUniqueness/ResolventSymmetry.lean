import Solutions.J0RadialUniqueness.ResolventParameterAnalytic

/-! Exact parameter symmetries of the actual kernels and their integrals.
For a complex input function, conjugation also conjugates that input. -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace J0RadialUniqueness

@[simp] theorem resolvent_conj_two : conj (2 : ℂ) = 2 := by
  apply Complex.ext <;> norm_num

@[simp] theorem resolvent_conj_four : conj (4 : ℂ) = 4 := by
  apply Complex.ext <;> norm_num

theorem Q_conj (w : ℂ) : Q (conj w) = conj (Q w) := by
  unfold Q
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  simp

theorem harmonicF_conj (w : ℂ) : harmonicF (conj w) = conj (harmonicF w) := by
  unfold harmonicF
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  simp only [map_mul, fTerm_conj, map_ratCast]

theorem harmonicDividedDifference_conj (w : ℂ) :
    harmonicDividedDifference (conj w) = conj (harmonicDividedDifference w) := by
  rw [harmonicDividedDifference_eq_series, harmonicDividedDifference_eq_series, Complex.conj_tsum]
  apply tsum_congr
  intro n
  simp [harmonicDividedTerm]

@[simp] theorem helmholtzResolventArg_neg (lam : ℂ) (s : ℝ) :
    helmholtzResolventArg (-lam) s = helmholtzResolventArg lam s := by
  simp [helmholtzResolventArg]

theorem helmholtzResolventArg_conj (lam : ℂ) (s : ℝ) :
    helmholtzResolventArg (conj lam) s = conj (helmholtzResolventArg lam s) := by
  simp [helmholtzResolventArg]

@[simp] theorem helmholtzP_neg (lam : ℂ) (s : ℝ) : helmholtzP (-lam) s = helmholtzP lam s := by
  simp only [helmholtzP_eq_F_arg, helmholtzResolventArg_neg]

@[simp] theorem helmholtzH_neg (lam : ℂ) (s : ℝ) : helmholtzH (-lam) s = helmholtzH lam s := by
  simp only [helmholtzH_eq_harmonicF, neg_sq]

theorem helmholtzP_conj (lam : ℂ) (s : ℝ) : helmholtzP (conj lam) s = conj (helmholtzP lam s) := by
  simp only [helmholtzP_eq_F_arg, helmholtzResolventArg_conj, F_conj]

theorem helmholtzH_conj (lam : ℂ) (s : ℝ) : helmholtzH (conj lam) s = conj (helmholtzH lam s) := by
  rw [helmholtzH_eq_harmonicF, helmholtzH_eq_harmonicF]
  change harmonicF (helmholtzResolventArg (conj lam) s) =
    conj (harmonicF (helmholtzResolventArg lam s))
  rw [helmholtzResolventArg_conj, harmonicF_conj]

@[simp] theorem helmholtzResolventB_neg (r : ℝ) (lam : ℂ) (s : ℝ) :
    helmholtzResolventB r (-lam) s = helmholtzResolventB r lam s := by
  simp only [helmholtzResolventB, helmholtzP_neg, helmholtzH_neg]

theorem helmholtzResolventB_conj (r : ℝ) (lam : ℂ) (s : ℝ) :
    helmholtzResolventB r (conj lam) s = conj (helmholtzResolventB r lam s) := by
  simp [helmholtzResolventB, helmholtzP_conj, helmholtzH_conj, helmholtzLogRatio]

@[simp] theorem helmholtzResolventT_neg (r : ℝ) (lam : ℂ) (s : ℝ) :
    helmholtzResolventT r (-lam) s = helmholtzResolventT r lam s := by
  simp only [helmholtzResolventT, helmholtzResolventArg_neg, helmholtzP_neg]

theorem helmholtzResolventT_conj (r : ℝ) (lam : ℂ) (s : ℝ) :
    helmholtzResolventT r (conj lam) s = conj (helmholtzResolventT r lam s) := by
  simp [helmholtzResolventT, helmholtzResolventArg_conj, helmholtzP_conj,
    Q_conj, harmonicDividedDifference_conj]

@[simp] theorem helmholtzResolventMass_neg (r : ℝ) (lam : ℂ) :
    helmholtzResolventMass r (-lam) = helmholtzResolventMass r lam := by
  simp only [helmholtzResolventMass, helmholtzResolventArg_neg]

theorem helmholtzResolventMass_conj (r : ℝ) (lam : ℂ) :
    helmholtzResolventMass r (conj lam) = conj (helmholtzResolventMass r lam) := by
  simp [helmholtzResolventMass, helmholtzResolventArg_conj, Q_conj]

@[simp] theorem planarHelmholtzResolventB_neg (r : ℝ) (lam : ℂ) (y : Plane) :
    planarHelmholtzResolventB r (-lam) y = planarHelmholtzResolventB r lam y := by
  simp only [planarHelmholtzResolventB, compactRadialComplexKernel, helmholtzResolventB_neg]

theorem planarHelmholtzResolventB_conj (r : ℝ) (lam : ℂ) (y : Plane) :
    planarHelmholtzResolventB r (conj lam) y = conj (planarHelmholtzResolventB r lam y) := by
  by_cases hy : ‖y‖ < r <;>
    simp [planarHelmholtzResolventB, compactRadialComplexKernel, helmholtzResolventB_conj, hy]

@[simp] theorem planarHelmholtzResolventT_neg (r : ℝ) (lam : ℂ) (y : Plane) :
    planarHelmholtzResolventT r (-lam) y = planarHelmholtzResolventT r lam y := by
  simp only [planarHelmholtzResolventT, compactRadialComplexKernel, helmholtzResolventT_neg]

theorem planarHelmholtzResolventT_conj (r : ℝ) (lam : ℂ) (y : Plane) :
    planarHelmholtzResolventT r (conj lam) y = conj (planarHelmholtzResolventT r lam y) := by
  by_cases hy : ‖y‖ < r <;>
    simp [planarHelmholtzResolventT, compactRadialComplexKernel, helmholtzResolventT_conj, hy]

@[simp] theorem planarResolventTConvolution_neg (r : ℝ) (u : Plane → ℂ) (x : Plane) (lam : ℂ) :
    planarResolventTConvolution r u x (-lam) = planarResolventTConvolution r u x lam := by
  simp only [planarResolventTConvolution, planarHelmholtzResolventT_neg]

theorem planarResolventTConvolution_conj (r : ℝ) (u : Plane → ℂ) (x : Plane) (lam : ℂ) :
    planarResolventTConvolution r (fun y => conj (u y)) x (conj lam) =
      conj (planarResolventTConvolution r u x lam) := by
  unfold planarResolventTConvolution
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by simp [planarHelmholtzResolventT_conj])

theorem ordinaryResolventQuotient_conj (r : ℝ) (u : Plane → ℂ) (x : Plane) (lam : ℂ) :
    planarResolventTConvolution r (fun y => conj (u y)) x (conj lam) /
        helmholtzResolventMass r (conj lam) =
      conj (planarResolventTConvolution r u x lam / helmholtzResolventMass r lam) := by
  rw [planarResolventTConvolution_conj, helmholtzResolventMass_conj, map_div₀]

theorem norm_ordinaryResolventQuotient_conj (r : ℝ) (u : Plane → ℂ) (x : Plane) (lam : ℂ) :
    ‖planarResolventTConvolution r u x (conj lam) / helmholtzResolventMass r (conj lam)‖ =
      ‖planarResolventTConvolution r (fun y => conj (u y)) x lam / helmholtzResolventMass r lam‖ := by
  have hh := congrArg norm
    (ordinaryResolventQuotient_conj r (fun y => conj (u y)) x lam)
  simpa only [starRingEnd_self_apply, Complex.norm_conj] using hh

end J0RadialUniqueness
