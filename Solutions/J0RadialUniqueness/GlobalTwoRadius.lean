import Solutions.J0RadialUniqueness.Main
import Solutions.J0RadialUniqueness.GlobalWeak
import Solutions.J0RadialUniqueness.GlobalWeyl
import Solutions.J0RadialUniqueness.Conditional.TwoRadius

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace J0RadialUniqueness

theorem paper_weyl_regularization : WeylRegularizationStatement := by
  intro f hf hweak
  exact global_weyl hf hweak

theorem paper_all_radius_mean_value : AllRadiusMeanValueStatement := by
  intro g hg r _ x
  exact circularMean_eq_of_harmonicOnNhd g hg r x

/-- The global application has only the substantive local two-radius theorem
left as an explicit argument; Weyl regularity and all-radius means are proved. -/
theorem globalTwoRadius_of_local (hloc : LocalTwoRadiusStatement) :
    GlobalTwoRadiusStatement := by
  intro r₁ r₂ f hr₁ hr₂ hne hf hm₁ hm₂
  have hweak := globalDistributionHarmonic_of_local hloc r₁ r₂ f hr₁ hr₂ hne hf hm₁ hm₂
  obtain ⟨g, hgs, hgh, hfg⟩ := global_weyl hf hweak
  refine ⟨hweak, ⟨g, hgs, hgh, hfg⟩, ?_⟩
  intro hfc
  exact continuous_harmonic_of_distribution hfc hweak

theorem globalTwoRadius_of_volchkov (hvolchkov : VolchkovLocalStatement) :
    GlobalTwoRadiusStatement :=
  globalTwoRadius_of_local (localTwoRadius_of_rayUniqueness_and_volchkov paper_5_3 hvolchkov)

end J0RadialUniqueness
