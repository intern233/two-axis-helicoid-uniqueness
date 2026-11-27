import TwoAxisHelicoid.TorusAntiholomorphicLifts
import TwoAxisHelicoid.TorusRemovableMap
import TwoAxisHelicoid.CompactPunctureHomeomorphism
import TwoAxisHelicoid.PuncturedLatticePlane
import TwoAxisHelicoid.ActualTorusManifoldImmersion

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology ComplexConjugate

theorem torus_antiholomorphic_of_continuous_off_puncture (L M : PeriodPair)
    {f : PeriodTorus L → PeriodTorus M} (hf : Continuous f)
    (hreg : ∀ z ∉ L.lattice, ∃ G : ℂ → ℂ, AnalyticAt ℂ G (conj z) ∧
      ∀ᶠ w in 𝓝 z, periodTorusProjection M (G (conj w)) = f (periodTorusProjection L w)) :
    TorusAntiholomorphic L M f := by
  obtain ⟨b,hb⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection M))
    (f (periodTorusProjection L 0))
  obtain ⟨F,hF,_,hl⟩ := torus_continuous_map_has_lift L M hf 0 b hb
  let K := fun z => F (conj z)
  have hK : Continuous K := hF.comp Complex.continuous_conj
  let D := conjugatePeriodPair L
  have hdiff (z : ℂ) (hz : z ∉ D.lattice) : DifferentiableAt ℂ K z := by
    obtain ⟨G,hG,he⟩ := hreg (conj z) (fun h => hz ((conjugatePeriodPair_mem_iff L z).mpr h))
    simp only [starRingEnd_self_apply] at hG
    have hcomp := Complex.continuous_conj.continuousAt.eventually he
    have hm : ∀ᶠ w in 𝓝 z, K w-G w ∈ M.lattice := by
      filter_upwards [hcomp] with w hw
      simp only [starRingEnd_self_apply] at hw
      exact (periodTorusProjection_eq_iff M (G w) (K w)).mp (hw.trans (hl (conj w)).symm)
    have hd := continuousAt_eventually_lattice_constant M (hK.continuousAt.sub hG.continuousAt) hm
    apply (hG.add analyticAt_const).differentiableAt.congr_of_eventuallyEq
      (f := fun w => G w+(K z-G z))
    filter_upwards [hd] with w hw
    change K w-G w = K z-G z at hw
    linear_combination hw
  intro z
  refine ⟨K,Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
    hK.continuousAt,Eventually.of_forall (fun w => by simpa [K] using hl w)⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (D.compl_lattice_sdiff_singleton_mem_nhds (conj z)),
    self_mem_nhdsWithin] with w hD hw
  exact hdiff w (fun h => hD ⟨h,hw⟩)

def PuncturedTorusAntiholomorphic (L M : PeriodPair) (f : PuncturedPeriodTorus L → PuncturedPeriodTorus M) :
    Prop := ∀ z ∉ L.lattice, ∃ G : ℂ → ℂ, AnalyticAt ℂ G (conj z) ∧
      ∀ᶠ w in 𝓝 z, ∀ hw : w ∉ L.lattice,
        periodTorusProjection M (G (conj w)) = (f (puncturedPlaneProjection L ⟨w,hw⟩)).1

/-- An actual antiholomorphic homeomorphism between punctured marked tori
extends antiholomorphically across the added ends. -/
theorem punctured_torus_anti_extension (L M : PeriodPair)
    (f : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus M) (hf : PuncturedTorusAntiholomorphic L M f) :
    TorusAntiholomorphic L M (compactPunctureExtension f) := by
  apply torus_antiholomorphic_of_continuous_off_puncture L M (compactPunctureExtension f).continuous
  intro z hz
  obtain ⟨G,hG,he⟩ := hf z hz
  refine ⟨G,hG,?_⟩
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz,he] with w hw hew
  exact (hew hw).trans (compactPunctureExtension_apply f (puncturedPlaneProjection L ⟨w,hw⟩)).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.punctured_torus_anti_extension
