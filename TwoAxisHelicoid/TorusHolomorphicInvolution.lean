import TwoAxisHelicoid.TorusActualLifts

namespace TwoAxisHelicoid
open Complex Set

/-- Every origin-fixing holomorphic map of an actual complex torus is induced
by a complex linear map of its covering plane. -/
theorem torus_holomorphic_fix_zero_linear (L : PeriodPair)
    {f : PeriodTorus L → PeriodTorus L} (hf : TorusHolomorphic L L f) (h0 : f 0 = 0) :
    ∃ c : ℂ, PreservesPeriodLattice L c ∧
      ∀ z, f (periodTorusProjection L z) = periodTorusProjection L (c*z) := by
  obtain ⟨F,hF,hF0,hl,hi⟩ := torus_holomorphic_map_has_entire_lift L L hf 0 0
    (by change (0 : PeriodTorus L) = f 0; exact h0.symm)
  obtain ⟨c,hc,hcL⟩ := entire_lattice_increment_fix_zero L hF hi hF0
  exact ⟨c,hcL,fun z => (hl z).symm.trans (congrArg (periodTorusProjection L) (hc z))⟩

/-- A nonidentity holomorphic involution fixing the origin of a genuine
complex torus is negation. The result is about the quotient map itself. -/
theorem torus_holomorphic_nontrivial_involution_negation (L : PeriodPair)
    {f : PeriodTorus L → PeriodTorus L} (hf : TorusHolomorphic L L f)
    (h0 : f 0 = 0) (hinv : Function.Involutive f) (hne : f ≠ id) :
    ∀ q, f q = -q := by
  obtain ⟨c,_,hc⟩ := torus_holomorphic_fix_zero_linear L hf h0
  have hm (z : ℂ) : c*(c*z)-z ∈ L.lattice := by
    apply (periodTorusProjection_eq_iff L z (c*(c*z))).mp
    rw [← hc,← hc]
    exact (hinv (periodTorusProjection L z)).symm
  have he := continuous_lattice_valued_constant L
    (show Continuous (fun z : ℂ => c*(c*z)-z) by fun_prop) hm 1 0
  have hcc : c*c = 1 := by simpa [sub_eq_zero] using he
  have hfac : (c-1)*(c+1) = 0 := by linear_combination hcc
  rcases mul_eq_zero.mp hfac with hp | hn
  · have hc1 : c = 1 := sub_eq_zero.mp hp
    exfalso
    apply hne
    funext q
    obtain ⟨z,rfl⟩ := Quotient.exists_rep q
    change f (periodTorusProjection L z) = periodTorusProjection L z
    simpa [hc1] using hc z
  · have hcn : c = -1 := eq_neg_of_add_eq_zero_left hn
    intro q
    obtain ⟨z,rfl⟩ := Quotient.exists_rep q
    change f (periodTorusProjection L z) = periodTorusProjection L (-z)
    rw [hc,hcn,neg_one_mul]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_holomorphic_nontrivial_involution_negation
