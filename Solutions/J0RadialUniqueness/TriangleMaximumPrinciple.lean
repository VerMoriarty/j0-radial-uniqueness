import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! Maximum modulus on a genuine closed triangle and exhaustion of the right
double sector by such triangles. These are general complex-analytic tools;
neither a growth assumption nor a two-radius conclusion is built into them. -/

noncomputable section

open Set Filter
open scoped Topology

namespace J0RadialUniqueness

def closedPrincipalTriangle (N : ℝ) : Set ℂ :=
  {z : ℂ | |z.im| ≤ z.re ∧ z.re ≤ N}

def closedRightPrincipalWedge : Set ℂ := {z : ℂ | |z.im| ≤ z.re}

theorem closedPrincipalTriangle_isClosed (N : ℝ) : IsClosed (closedPrincipalTriangle N) := by
  change IsClosed ({z : ℂ | |z.im| ≤ z.re} ∩ {z : ℂ | z.re ≤ N})
  exact (isClosed_le Complex.continuous_im.abs Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)

theorem norm_le_twice_of_mem_closedPrincipalTriangle {N : ℝ} {z : ℂ}
    (hz : z ∈ closedPrincipalTriangle N) : ‖z‖ ≤ 2 * N := by
  have hre : 0 ≤ z.re := (abs_nonneg z.im).trans hz.1
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ = z.re + |z.im| := by rw [abs_of_nonneg hre]
    _ ≤ 2 * N := by linarith [hz.1, hz.2]

theorem closedPrincipalTriangle_subset_closedBall (N : ℝ) :
    closedPrincipalTriangle N ⊆ Metric.closedBall (0 : ℂ) (2 * N) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_twice_of_mem_closedPrincipalTriangle hz

theorem closedPrincipalTriangle_isCompact (N : ℝ) : IsCompact (closedPrincipalTriangle N) :=
  (isCompact_closedBall (0 : ℂ) (2 * N)).of_isClosed_subset
    (closedPrincipalTriangle_isClosed N) (closedPrincipalTriangle_subset_closedBall N)

/-- Two strict inequalities give a genuine open neighborhood inside the triangle. -/
theorem mem_interior_closedPrincipalTriangle_of_strict {N : ℝ} {z : ℂ}
    (hside : |z.im| < z.re) (hvertical : z.re < N) :
    z ∈ interior (closedPrincipalTriangle N) := by
  have hopen : IsOpen {w : ℂ | |w.im| < w.re ∧ w.re < N} :=
    (isOpen_lt Complex.continuous_im.abs Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hsub : {w : ℂ | |w.im| < w.re ∧ w.re < N} ⊆ closedPrincipalTriangle N :=
    fun w hw => ⟨hw.1.le, hw.2.le⟩
  exact interior_maximal hsub hopen ⟨hside, hvertical⟩

/-- Every frontier point is on one of the actual three line segments. -/
theorem mem_frontier_closedPrincipalTriangle_cases {N : ℝ} {z : ℂ}
    (hz : z ∈ frontier (closedPrincipalTriangle N)) :
    (|z.im| = z.re ∧ 0 ≤ z.re ∧ z.re ≤ N) ∨ (z.re = N ∧ |z.im| ≤ N) := by
  have hmem : z ∈ closedPrincipalTriangle N := (closedPrincipalTriangle_isClosed N).frontier_subset hz
  have hre : 0 ≤ z.re := (abs_nonneg z.im).trans hmem.1
  by_cases hside : |z.im| = z.re
  · exact Or.inl ⟨hside, hre, hmem.2⟩
  · by_cases hvertical : z.re = N
    · exact Or.inr ⟨hvertical, hvertical ▸ hmem.1⟩
    · have hs : |z.im| < z.re := (lt_or_eq_of_le hmem.1).resolve_right hside
      have hv : z.re < N := (lt_or_eq_of_le hmem.2).resolve_right hvertical
      exact False.elim (((mem_frontier_iff_notMem_interior hmem).mp hz)
        (mem_interior_closedPrincipalTriangle_of_strict hs hv))

/-- The actual complex maximum-modulus principle on a closed triangle.
The same statement remains valid for degenerate or empty triangles. -/
theorem norm_le_on_closedPrincipalTriangle {q : ℂ → ℂ}
    (hq : Differentiable ℂ q) {N C : ℝ}
    (hside : ∀ z : ℂ, |z.im| = z.re → 0 ≤ z.re → z.re ≤ N → ‖q z‖ ≤ C)
    (hvertical : ∀ z : ℂ, z.re = N → |z.im| ≤ N → ‖q z‖ ≤ C) :
    ∀ z ∈ closedPrincipalTriangle N, ‖q z‖ ≤ C := by
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (closedPrincipalTriangle_isCompact N).isBounded hq.diffContOnCl
    (fun w hw => ?_) (subset_closure hz)
  rcases mem_frontier_closedPrincipalTriangle_cases hw with hs | hv
  · exact hside w hs.1 hs.2.1 hs.2.2
  · exact hvertical w hv.1 hv.2

/-- A boundary estimate with one constant on an exhausting family of actual
triangles bounds the entire function on the full closed right double sector. -/
theorem norm_le_on_rightPrincipalWedge_of_triangle_exhaustion {q : ℂ → ℂ}
    (hq : Differentiable ℂ q) (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) {C : ℝ}
    (hside : ∀ n : ℕ, ∀ z : ℂ,
      |z.im| = z.re → 0 ≤ z.re → z.re ≤ N n → ‖q z‖ ≤ C)
    (hvertical : ∀ n : ℕ, ∀ z : ℂ, z.re = N n → |z.im| ≤ N n → ‖q z‖ ≤ C) :
    ∀ z ∈ closedRightPrincipalWedge, ‖q z‖ ≤ C := by
  intro z hz
  have hlarge : ∀ᶠ n : ℕ in atTop, z.re ≤ N n :=
    hN.eventually (eventually_ge_atTop z.re)
  obtain ⟨n, hn⟩ := hlarge.exists
  exact norm_le_on_closedPrincipalTriangle hq (hside n) (hvertical n) z ⟨hz, hn⟩

/-- A version where the sloping-ray bound is stated just once, independently
of the truncation index. -/
theorem norm_le_on_rightPrincipalWedge_of_uniform_sides {q : ℂ → ℂ}
    (hq : Differentiable ℂ q) (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) {C : ℝ}
    (hside : ∀ z : ℂ, |z.im| = z.re → 0 ≤ z.re → ‖q z‖ ≤ C)
    (hvertical : ∀ n : ℕ, ∀ z : ℂ, z.re = N n → |z.im| ≤ N n → ‖q z‖ ≤ C) :
    ∀ z ∈ closedRightPrincipalWedge, ‖q z‖ ≤ C :=
  norm_le_on_rightPrincipalWedge_of_triangle_exhaustion hq N hN
    (fun _ z hsidez hre _ => hside z hsidez hre) hvertical

end J0RadialUniqueness
