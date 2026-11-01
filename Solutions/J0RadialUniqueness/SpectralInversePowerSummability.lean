import Solutions.J0RadialUniqueness.SpectralRootCounting
import Solutions.J0RadialUniqueness.ZeroFree
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-! Inverse-power summability over the complete actual Bessel one-point set.
The proof partitions the roots into dyadic shells. Each shell is finite by the
proved compact zero theorem; its cardinality satisfies the actual Jensen bound.
The resulting shell sums are dominated by a geometric series. -/

noncomputable section
open Set Filter Metric
open scoped Topology Classical

namespace J0RadialUniqueness

def dyadicRadiusShell {α : Type*} (ρ : α → ℝ) (n : ℕ) : Set α :=
  {a | (2 : ℝ) ^ n ≤ ρ a ∧ ρ a < (2 : ℝ) ^ (n + 1)}

theorem dyadicRadiusShell_partition {α : Type*} {ρ : α → ℝ}
    (hρ : ∀ a, 1 ≤ ρ a) : ∀ a, ∃! n : ℕ, a ∈ dyadicRadiusShell ρ n := by
  intro a
  change ∃! n : ℕ, (2 : ℝ) ^ n ≤ ρ a ∧ ρ a < (2 : ℝ) ^ (n + 1)
  obtain ⟨n, hn⟩ := exists_nat_pow_near (hρ a) (by norm_num : 1 < (2 : ℝ))
  refine ⟨n, hn, fun m hm => ?_⟩
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hp : (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ n :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hmn)
    exact False.elim ((not_lt_of_ge (hp.trans hn.1)) hm.2)
  · exact hmn
  · have hp : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ m :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hnm)
    exact False.elim ((not_lt_of_ge (hp.trans hm.1)) hn.2)

theorem dyadic_inverse_power_identity (ε : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ n) ^ (-1 - ε) =
      2 * ((2 : ℝ) ^ (-ε)) ^ n := by
  rw [pow_succ]
  calc
    ((2 : ℝ) ^ n * 2) * ((2 : ℝ) ^ n) ^ (-1 - ε) =
        2 * (((2 : ℝ) ^ n) ^ (1 : ℝ) * ((2 : ℝ) ^ n) ^ (-1 - ε)) := by
      rw [Real.rpow_one]
      ring
    _ = 2 * ((2 : ℝ) ^ n) ^ (1 + (-1 - ε)) := by
      rw [Real.rpow_add (by positivity : 0 < (2 : ℝ) ^ n)]
    _ = 2 * ((2 : ℝ) ^ n) ^ (-ε) := by
      congr 2
      ring
    _ = 2 * ((2 : ℝ) ^ (-ε)) ^ n := by
      rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)) n (-ε),
        mul_comm (n : ℝ) (-ε), Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ)) (-ε) n]

/-- A reusable dyadic comparison lemma. All counting hypotheses are explicit
generic inputs here; the paper's actual spectrum is connected below. -/
theorem summable_inverse_power_of_linear_dyadic_count {α : Type*} {ρ : α → ℝ}
    (hρ : ∀ a, 1 ≤ ρ a) {C ε : ℝ} (_hC : 0 ≤ C) (hε : 0 < ε)
    (hfinite : ∀ n : ℕ, {a | ρ a ≤ (2 : ℝ) ^ (n + 1)}.Finite)
    (hcount : ∀ n : ℕ,
      ({a | ρ a ≤ (2 : ℝ) ^ (n + 1)}.ncard : ℝ) ≤ C * (2 : ℝ) ^ (n + 1)) :
    Summable (fun a : α => (ρ a) ^ (-1 - ε)) := by
  classical
  let s : ℕ → Set α := dyadicRadiusShell ρ
  have hsfinite (n : ℕ) : (s n).Finite :=
    (hfinite n).subset (fun _ ha => ha.2.le)
  have hsummable (n : ℕ) : Summable (fun a : s n => (ρ a) ^ (-1 - ε)) :=
    (hsfinite n).summable (fun a : α => (ρ a) ^ (-1 - ε))
  have hgeometric : Summable (fun n : ℕ =>
      (2 * C) * (((2 : ℝ) ^ (-ε)) ^ n)) :=
    (summable_geometric_of_lt_one
      (Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (-ε))
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith))).mul_left _
  have hshellbound (n : ℕ) : (∑' a : s n, (ρ a) ^ (-1 - ε)) ≤
      (2 * C) * (((2 : ℝ) ^ (-ε)) ^ n) := by
    letI := (hsfinite n).fintype
    have hsub : s n ⊆ {a | ρ a ≤ (2 : ℝ) ^ (n + 1)} := fun _ ha => ha.2.le
    have hcard : ((s n).ncard : ℝ) ≤ C * (2 : ℝ) ^ (n + 1) := by
      have hh : (s n).ncard ≤ {a | ρ a ≤ (2 : ℝ) ^ (n + 1)}.ncard :=
        Set.ncard_le_ncard hsub (hfinite n)
      exact (Nat.cast_le.mpr hh).trans (hcount n)
    calc
      (∑' a : s n, (ρ a) ^ (-1 - ε)) = ∑ a : s n, (ρ a) ^ (-1 - ε) := tsum_fintype _
      _ ≤ ∑ _a : s n, ((2 : ℝ) ^ n) ^ (-1 - ε) := by
        apply Finset.sum_le_sum
        intro a _
        exact Real.rpow_le_rpow_of_nonpos (by positivity) a.property.1 (by linarith)
      _ = ((s n).ncard : ℝ) * ((2 : ℝ) ^ n) ^ (-1 - ε) := by simp
      _ ≤ (C * (2 : ℝ) ^ (n + 1)) * ((2 : ℝ) ^ n) ^ (-1 - ε) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by positivity) _)
      _ = (2 * C) * (((2 : ℝ) ^ (-ε)) ^ n) := by
        calc
          _ = C * ((2 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ n) ^ (-1 - ε)) := by ring
          _ = _ := by rw [dyadic_inverse_power_identity]; ring
  have hsumShells : Summable (fun n : ℕ => ∑' a : s n, (ρ a) ^ (-1 - ε)) :=
    Summable.of_nonneg_of_le
      (fun _ => tsum_nonneg fun a => Real.rpow_nonneg
        (le_trans zero_le_one (hρ a)) _) hshellbound hgeometric
  exact (summable_partition (f := fun a : α => (ρ a) ^ (-1 - ε))
    (fun a => Real.rpow_nonneg (le_trans zero_le_one (hρ a)) _)
    (dyadicRadiusShell_partition hρ)).mpr ⟨hsummable, hsumShells⟩

theorem onePoints_norm_bounded_finite (R : ℝ) :
    {z : onePoints | ‖(z : ℂ)‖ ≤ R}.Finite := by
  have hp := (onePoints_inter_closedBall_finite R).preimage
    (f := fun z : onePoints => (z : ℂ)) (fun _ _ _ _ h => Subtype.ext h)
  convert! hp using 1
  ext z
  simp only [mem_setOf_eq, mem_preimage, mem_inter_iff, z.property, true_and,
    mem_closedBall, dist_zero_right]

theorem onePoints_norm_bounded_ncard_le {R : ℝ} (hR : 0 < R) :
    ({z : onePoints | ‖(z : ℂ)‖ ≤ R}.ncard : ℝ) ≤ (2 / Real.log 2) * R := by
  have he : {z : onePoints | ‖(z : ℂ)‖ ≤ R} =
      {z : onePoints | (z : ℂ) ∈ closedBall (0 : ℂ) R} := by
    ext z
    simp only [mem_setOf_eq, mem_closedBall, dist_zero_right]
  rw [he, Set.ncard_subtype]
  have hset : closedBall (0 : ℂ) R ∩ {x : ℂ | x ∈ onePoints} =
      onePoints ∩ closedBall (0 : ℂ) R := by
    ext x
    exact and_comm
  rw [hset]
  exact onePoints_inter_closedBall_ncard_le hR

/-- The full actual one-point set satisfies the inverse-power summability
required before selecting the right-half-plane enumeration in Volchkov's
Lemma 1(a). No root enumeration or new spectral estimate is assumed. -/
theorem onePoints_inverse_power_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (fun z : onePoints => ‖(z : ℂ)‖ ^ (-1 - ε)) := by
  have hnorm : ∀ z : onePoints, 1 ≤ ‖(z : ℂ)‖ := by
    intro z
    exact (by norm_num : (1 : ℝ) ≤ 4).trans
      (one_point_norm_ge_four z z.property.1 z.property.2)
  have hC : 0 ≤ 2 / Real.log 2 :=
    div_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  exact summable_inverse_power_of_linear_dyadic_count
    (ρ := fun z : onePoints => ‖(z : ℂ)‖) (C := 2 / Real.log 2) hnorm hC hε
    (fun _ => onePoints_norm_bounded_finite _)
    (fun _ => onePoints_norm_bounded_ncard_le (by positivity))

end J0RadialUniqueness
