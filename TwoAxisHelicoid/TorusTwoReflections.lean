import TwoAxisHelicoid.TorusHolomorphicInvolution
import TwoAxisHelicoid.TorusRealStructureNormalization
import TwoAxisHelicoid.RhombicReflectionIntersection

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

theorem torus_antiholomorphic_comp_holomorphic (L : PeriodPair)
    {f g : PeriodTorus L → PeriodTorus L}
    (hf : TorusAntiholomorphic L L f) (hg : TorusAntiholomorphic L L g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) : TorusHolomorphic L L (f ∘ g) := by
  obtain ⟨c,_,hc⟩ := torus_antiholomorphic_fix_zero_antilinear L hf hf0
  obtain ⟨d,_,hd⟩ := torus_antiholomorphic_fix_zero_antilinear L hg hg0
  intro z
  refine ⟨fun w => (c*conj d)*w,analyticAt_const.mul analyticAt_id,?_⟩
  apply Filter.Eventually.of_forall
  intro w
  dsimp only [Function.comp_def]
  rw [hd,hc,map_mul,starRingEnd_self_apply,mul_assoc]

theorem torus_two_reflections_comp_negation (L : PeriodPair)
    {f g : PeriodTorus L → PeriodTorus L}
    (hf : TorusAntiholomorphic L L f) (hg : TorusAntiholomorphic L L g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfi : Function.Involutive f) (hgi : Function.Involutive g)
    (hcomm : Function.Commute f g) (hne : f ≠ g) : ∀ q, f (g q) = -q := by
  apply torus_holomorphic_nontrivial_involution_negation L
    (torus_antiholomorphic_comp_holomorphic L hf hg hf0 hg0)
    (by simp [hg0,hf0])
  · intro q
    change f (g (f (g q))) = q
    rw [← hcomm (g q),hfi,hgi]
  · intro he
    apply hne
    funext q
    have h := congrFun he (g q)
    change f (g (g q)) = g q at h
    rw [hgi q] at h
    exact h

theorem periodTorusScalingHomeomorph_neg (L M : PeriodPair) (c : ℂ) (hc : c ≠ 0)
    (hp : ∀ z : ℂ, z ∈ L.lattice ↔ c*z ∈ M.lattice) (q : PeriodTorus L) :
    periodTorusScalingHomeomorph L M c hc hp (-q) =
      -periodTorusScalingHomeomorph L M c hc hp q := by
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  change periodTorusProjection M (c*(-z)) = periodTorusProjection M (-(c*z))
  rw [mul_neg]

theorem rhombicHorizontalReflection_neg {t : ℝ} (ht : 0 < t)
    (q : PeriodTorus (rhombicPeriodPair t ht)) :
    rhombicHorizontalReflection ht (-q) = -rhombicHorizontalReflection ht q := by
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  change periodTorusProjection (rhombicPeriodPair t ht) (conj (-z)) =
    periodTorusProjection (rhombicPeriodPair t ht) (-conj z)
  rw [map_neg]

theorem rhombicHorizontalReflection_involutive {t : ℝ} (ht : 0 < t) :
    Function.Involutive (rhombicHorizontalReflection ht) :=
  periodTorusConjugation_involutive _ _

/-- Both actual commuting reflections can be normalized simultaneously; their
composition and the second reflection need not be postulated in coordinates. -/
theorem torus_two_reflections_rhombic_normalization (L : PeriodPair)
    {f g : PeriodTorus L → PeriodTorus L}
    (hf : TorusAntiholomorphic L L f) (hg : TorusAntiholomorphic L L g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfi : Function.Involutive f) (hgi : Function.Involutive g)
    (hcomm : Function.Commute f g) (hne : f ≠ g)
    (hconn : IsPreconnected {q : PeriodTorus L | f q = q}) :
    ∃ (s : ℂ) (t : ℝ) (hs : s ≠ 0) (ht : 0 < t)
      (hp : ∀ z : ℂ, z ∈ L.lattice ↔ s*z ∈ (rhombicPeriodPair t ht).lattice),
      let e := periodTorusScalingHomeomorph L (rhombicPeriodPair t ht) s hs hp
      (∀ q, e (f q) = rhombicHorizontalReflection ht (e q)) ∧
      (∀ q, e (g q) = rhombicVerticalReflection ht (e q)) := by
  obtain ⟨s,t,hs,ht,hp,he⟩ := torus_real_structure_rhombic_normalization L hf hf0 hfi hconn
  refine ⟨s,t,hs,ht,hp,he,?_⟩
  let e := periodTorusScalingHomeomorph L (rhombicPeriodPair t ht) s hs hp
  have hcomp := torus_two_reflections_comp_negation L hf hg hf0 hg0 hfi hgi hcomm hne
  intro q
  have hh : rhombicHorizontalReflection ht (e (g q)) = -e q := by
    rw [← he,hcomp,periodTorusScalingHomeomorph_neg]
  have h := congrArg (rhombicHorizontalReflection ht) hh
  rw [rhombicHorizontalReflection_involutive ht,rhombicHorizontalReflection_neg] at h
  exact h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_two_reflections_rhombic_normalization
