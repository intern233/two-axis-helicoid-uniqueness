import TwoAxisHelicoid.TorusPathIntegrals
import TwoAxisHelicoid.PeriodTorusConjugation

namespace TwoAxisHelicoid
open Complex Set

/-- Translate an actual lifted arc by any deck transformation. -/
noncomputable def ComplexPeriodArc.translateLattice {L : PeriodPair}
    (a : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ) (ω : ℂ) (hω : ω ∈ L.lattice) :
    ComplexPeriodArc (L.lattice : Set ℂ)ᶜ where
  left := a.left
  right := a.right
  ordered := a.ordered
  curve s := a.curve s+ω
  velocity := a.velocity
  stays := fun s hs h => a.stays hs (by simpa using L.lattice.sub_mem h hω)
  continuous_curve := a.continuous_curve.add continuousOn_const
  continuous_velocity := a.continuous_velocity
  derivative s hs := (a.derivative s hs).add_const ω

theorem ComplexPeriodArc.translateLattice_integral {L : PeriodPair}
    (a : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ) {ω : ℂ} (hω : ω ∈ L.lattice) {f : ℂ → ℂ}
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z) :
    (a.translateLattice ω hω).integral f = a.integral f := by
  simp only [integral,translateLattice,hp _ _ hω]

/-- Every integral on an actual quotient path has an unbroken chain of
lifts starting at any selected representative. This does not require
regularity of the differential at the removed lattice. -/
theorem TorusPathIntegral.coherent_lift {L : PeriodPair} {f : ℂ → ℂ}
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z)
    {q r : PuncturedPeriodTorus L} {γ : Path q r} {v : ℂ} (hv : TorusPathIntegral L f γ v)
    (x : ℂ) (hx : periodTorusProjection L x = q.1) :
    ∃ y : ℂ, periodTorusProjection L y = r.1 ∧
      ∃ p : PiecewiseComplexPath (L.lattice : Set ℂ)ᶜ x y, p.integral f = v := by
  induction hv generalizing x with
  | refl q =>
    have hn : x ∉ L.lattice := fun h => q.2 (hx.symm.trans ((periodTorusProjection_eq_zero L x).mpr h))
    exact ⟨x,hx,.refl _ hn,rfl⟩
  | @arc q r γ a he =>
    have hq := he 0
    have hr := he 1
    simp only [γ.source,γ.target,ComplexPeriodArc.time,Set.Icc.coe_zero,Set.Icc.coe_one,
      AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] at hq hr
    let ω := x-a.curve a.left
    have hω : ω ∈ L.lattice := (periodTorusProjection_eq_iff _ _ _).mp (hq.symm.trans hx.symm)
    let b := a.translateLattice ω hω
    have hleft : b.curve b.left = x := by change a.curve a.left+(x-a.curve a.left) = x; ring
    have hright : periodTorusProjection L (b.curve b.right) = r.1 :=
      (periodTorusProjection_add_lattice L _ _ hω).trans hr.symm
    refine ⟨_,hright,?_⟩
    generalize heq : x = u
    have hb : b.curve b.left = u := hleft.trans heq
    rw [← hb]
    exact ⟨.arc b,a.translateLattice_integral hω hp⟩
  | @trans p q r γ δ v w _ _ ih₁ ih₂ =>
    obtain ⟨u,hu,P,hP⟩ := ih₁ x hx
    obtain ⟨y,hy,Q,hQ⟩ := ih₂ u hu
    exact ⟨y,hy,.trans P Q,congrArg₂ (·+·) hP hQ⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.TorusPathIntegral.coherent_lift
