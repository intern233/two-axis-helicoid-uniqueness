import TwoAxisHelicoid.TorusRemovableMap
import TwoAxisHelicoid.CompactPunctureHomeomorphism
import TwoAxisHelicoid.PuncturedLatticePlane
import TwoAxisHelicoid.TorusHolomorphicInvolution
import TwoAxisHelicoid.ActualTorusManifoldImmersion

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology

def PuncturedTorusHolomorphic (L M : PeriodPair) (f : PuncturedPeriodTorus L → PuncturedPeriodTorus M) :
    Prop := ∀ z ∉ L.lattice, ∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧
      ∀ᶠ w in 𝓝 z, ∀ hw : w ∉ L.lattice,
        periodTorusProjection M (G w) = (f (puncturedPlaneProjection L ⟨w,hw⟩)).1

theorem punctured_torus_holomorphic_extension (L M : PeriodPair)
    (f : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus M) (hf : PuncturedTorusHolomorphic L M f) :
    TorusHolomorphic L M (compactPunctureExtension f) := by
  apply torus_holomorphic_of_continuous_off_puncture L M (compactPunctureExtension f).continuous
  intro z hz
  obtain ⟨G,hG,he⟩ := hf z hz
  refine ⟨G,hG,?_⟩
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz,he] with w hw hew
  exact (hew hw).trans (compactPunctureExtension_apply f (puncturedPlaneProjection L ⟨w,hw⟩)).symm

/-- Every biholomorphic automorphism of the actual punctured torus is
induced by a lattice automultiplier on its covering plane. -/
theorem punctured_torus_automorphism_linear (L : PeriodPair)
    (f : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus L)
    (hf : PuncturedTorusHolomorphic L L f) (hg : PuncturedTorusHolomorphic L L f.symm) :
    ∃ c : ℂ, PeriodLatticeAutomultiplier L c ∧ ∀ z (hz : z ∉ L.lattice),
      (f (puncturedPlaneProjection L ⟨z,hz⟩)).1 = periodTorusProjection L (c*z) := by
  let F := compactPunctureExtension f
  let G := compactPunctureExtension f.symm
  obtain ⟨c,hc,hf'⟩ := torus_holomorphic_fix_zero_linear L
    (punctured_torus_holomorphic_extension L L f hf) (compactPunctureExtension_at_end f)
  obtain ⟨d,hd,hg'⟩ := torus_holomorphic_fix_zero_linear L
    (punctured_torus_holomorphic_extension L L f.symm hg) (compactPunctureExtension_at_end f.symm)
  have hleft (q : PeriodTorus L) : G (F q) = q := by
    by_cases he : q = 0
    · rw [he,show F 0 = 0 from compactPunctureExtension_at_end f,
        show G 0 = 0 from compactPunctureExtension_at_end f.symm]
    · let x : PuncturedPeriodTorus L := ⟨q,he⟩
      rw [show F q = (f x).1 from compactPunctureExtension_apply f x,
        show G (f x).1 = (f.symm (f x)).1 from compactPunctureExtension_apply f.symm (f x),
        f.symm_apply_apply]
  have hm (z : ℂ) : d*(c*z)-z ∈ L.lattice := by
    apply (periodTorusProjection_eq_iff L z (d*(c*z))).mp
    rw [← hg',← hf']
    exact (hleft _).symm
  have he := continuous_lattice_valued_constant L
    (show Continuous (fun z : ℂ => d*(c*z)-z) by fun_prop) hm 1 0
  have hdc : d*c = 1 := sub_eq_zero.mp (by simpa using he)
  have hcn : c ≠ 0 := fun h => by simp [h] at hdc
  have hdi : d = c⁻¹ := mul_right_cancel₀ hcn (hdc.trans (inv_mul_cancel₀ hcn).symm)
  refine ⟨c,⟨hcn,hc,hdi ▸ hd⟩,fun z hz => ?_⟩
  exact (compactPunctureExtension_apply f (puncturedPlaneProjection L ⟨z,hz⟩)).symm.trans (hf' z)

/-- A pointwise continuous family of biholomorphic automorphisms of a
punctured torus is constant on a connected parameter space. No continuous
choice of lifts of the family is assumed. -/
theorem continuous_punctured_torus_automorphisms_constant {I : Type*} [TopologicalSpace I]
    [PreconnectedSpace I] (L : PeriodPair) (f : I → PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus L)
    (hf : ∀ t, PuncturedTorusHolomorphic L L (f t))
    (hg : ∀ t, PuncturedTorusHolomorphic L L (f t).symm)
    (hc : ∀ q, Continuous (fun t => f t q)) (s t : I) (q : PuncturedPeriodTorus L) : f s q = f t q := by
  obtain ⟨⟨z,hz⟩,rfl⟩ := puncturedPlaneProjection_surjective L q
  let a : I → PeriodTorus L := fun i => (f i (puncturedPlaneProjection L ⟨z,hz⟩)).1
  have ha : Continuous a := continuous_subtype_val.comp (hc _)
  have hfin : (range a).Finite := by
    apply ((period_lattice_automultipliers_finite L).image
      (fun c => periodTorusProjection L (c*z))).subset
    rintro _ ⟨i,rfl⟩
    obtain ⟨c,hc',he⟩ := punctured_torus_automorphism_linear L (f i) (hf i) (hg i)
    exact ⟨c,hc',(he z hz).symm⟩
  exact Subtype.ext ((isPreconnected_range ha).isDiscrete_iff_subsingleton.mp hfin.isDiscrete
    ⟨s,rfl⟩ ⟨t,rfl⟩)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.continuous_punctured_torus_automorphisms_constant
