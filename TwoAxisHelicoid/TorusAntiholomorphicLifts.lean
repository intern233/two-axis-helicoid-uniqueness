import TwoAxisHelicoid.TorusActualLifts
import TwoAxisHelicoid.TransformedPeriodPair
import TwoAxisHelicoid.LatticeAffineMaps

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate

/-- Antiholomorphicity in the actual quotient coordinates. -/
def TorusAntiholomorphic (L M : PeriodPair) (f : PeriodTorus L → PeriodTorus M) : Prop :=
  ∀ z : ℂ, ∃ G : ℂ → ℂ, AnalyticAt ℂ G (conj z) ∧
    ∀ᶠ w in 𝓝 z, periodTorusProjection M (G (conj w)) = f (periodTorusProjection L w)

theorem TorusAntiholomorphic.continuous {L M : PeriodPair}
    {f : PeriodTorus L → PeriodTorus M} (hf : TorusAntiholomorphic L M f) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  obtain ⟨G,hG,he⟩ := hf z
  apply QuotientAddGroup.isOpenQuotientMap_mk.continuousAt_comp_iff.mp
  exact ((QuotientAddGroup.continuous_mk.continuousAt).comp
    (hG.continuousAt.comp Complex.continuous_conj.continuousAt)).congr he

theorem torus_antiholomorphic_continuous_lift {L M : PeriodPair}
    {f : PeriodTorus L → PeriodTorus M} (hf : TorusAntiholomorphic L M f)
    {F : ℂ → ℂ} (hF : Continuous F)
    (hlift : ∀ z, periodTorusProjection M (F z) = f (periodTorusProjection L z)) :
    Differentiable ℂ (fun z => F (conj z)) := by
  intro z
  obtain ⟨G,hG,he⟩ := hf (conj z)
  simp only [starRingEnd_self_apply] at hG
  have hp := Complex.continuous_conj.continuousAt.eventually he
  have hm : ∀ᶠ w in 𝓝 z, F (conj w)-G w ∈ M.lattice := by
    filter_upwards [hp] with w hw
    simp only [starRingEnd_self_apply] at hw
    apply (periodTorusProjection_eq_iff M (G w) (F (conj w))).mp
    exact hw.trans (hlift (conj w)).symm
  have hd := continuousAt_eventually_lattice_constant M
    ((hF.comp Complex.continuous_conj).continuousAt.sub hG.continuousAt) hm
  have heq : (fun w => G w+(F (conj z)-G z)) =ᶠ[𝓝 z] (fun w => F (conj w)) := by
    filter_upwards [hd] with w hw
    change F (conj w)-G w = F (conj z)-G z at hw
    linear_combination -hw
  exact ((hG.add analyticAt_const).congr heq).differentiableAt

/-- An actual antiholomorphic origin-fixing torus map has an antilinear lift;
existence of the lift and its affine form are proved, not assumed. -/
theorem torus_antiholomorphic_fix_zero_antilinear (L : PeriodPair)
    {f : PeriodTorus L → PeriodTorus L} (hf : TorusAntiholomorphic L L f) (h0 : f 0 = 0) :
    ∃ c : ℂ, (∀ ω ∈ L.lattice, c*conj ω ∈ L.lattice) ∧
      ∀ z, f (periodTorusProjection L z) = periodTorusProjection L (c*conj z) := by
  obtain ⟨F,hF,hF0,hl⟩ := torus_continuous_map_has_lift L L hf.continuous 0 0
    (by change (0 : PeriodTorus L) = f 0; exact h0.symm)
  have hinc : ∀ ω ∈ (conjugatePeriodPair L).lattice,
      ∃ v : ℂ, ∀ z, F (conj (z+ω)) = F (conj z)+v := by
    intro ω hω
    obtain ⟨v,_,hv⟩ := torus_continuous_lift_lattice_increments L L hF hl (conj ω)
      ((conjugatePeriodPair_mem_iff L ω).mp hω)
    exact ⟨v,fun z => by simpa using hv (conj z)⟩
  obtain ⟨c,d,he⟩ := entire_complex_lattice_increments_affine (conjugatePeriodPair L)
    (torus_antiholomorphic_continuous_lift hf hF hl) hinc
  have hd : d = 0 := by simpa [hF0] using (he 0).symm
  have hFlinear (z : ℂ) : F z = c*conj z := by simpa [hd] using he (conj z)
  have hformula (z : ℂ) : f (periodTorusProjection L z) = periodTorusProjection L (c*conj z) := by
    rw [← hl,hFlinear]
  refine ⟨c,?_,hformula⟩
  intro ω hω
  apply (periodTorusProjection_eq_zero L _).mp
  rw [← hformula,(periodTorusProjection_eq_zero L ω).mpr hω,h0]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_antiholomorphic_fix_zero_antilinear
