import TwoAxisHelicoid.TorusActualLifts
import Mathlib.Analysis.Complex.RemovableSingularity

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology

/-- A continuous map between two marked tori, holomorphic away from the
puncture in quotient coordinates, is holomorphic on the compactification. -/
theorem torus_holomorphic_of_continuous_off_puncture (L M : PeriodPair)
    {f : PeriodTorus L → PeriodTorus M} (hf : Continuous f)
    (hreg : ∀ z ∉ L.lattice, ∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧
      ∀ᶠ w in 𝓝 z, periodTorusProjection M (G w) = f (periodTorusProjection L w)) :
    TorusHolomorphic L M f := by
  obtain ⟨b,hb⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection M))
    (f (periodTorusProjection L 0))
  obtain ⟨F,hF,_,hl⟩ := torus_continuous_map_has_lift L M hf 0 b hb
  have hdiff (z : ℂ) (hz : z ∉ L.lattice) : DifferentiableAt ℂ F z := by
    obtain ⟨G,hG,hg⟩ := hreg z hz
    have hm : ∀ᶠ w in 𝓝 z, F w-G w ∈ M.lattice := by
      filter_upwards [hg] with w hw
      exact (periodTorusProjection_eq_iff M (G w) (F w)).mp (hw.trans (hl w).symm)
    have hd := continuousAt_eventually_lattice_constant M (hF.continuousAt.sub hG.continuousAt) hm
    apply (hG.add analyticAt_const).differentiableAt.congr_of_eventuallyEq
      (f := fun w => G w+(F z-G z))
    filter_upwards [hd] with w hw
    change F w-G w = F z-G z at hw
    linear_combination hw
  intro z
  refine ⟨F,Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
    hF.continuousAt,Eventually.of_forall hl⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds z),
    self_mem_nhdsWithin] with w hL hw
  exact hdiff w (fun h => hL ⟨h,hw⟩)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_holomorphic_of_continuous_off_puncture
