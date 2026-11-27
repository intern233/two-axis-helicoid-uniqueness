import TwoAxisHelicoid.RegularPlaneCutSpinParity
import TwoAxisHelicoid.HelicoidalTorusSpinParity
import TwoAxisHelicoid.SmoothTorusCurveLift
import TwoAxisHelicoid.TorusFundamentalGenerators

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- A parametrized smooth closed curve representing a nonidentity
element of the fundamental group has a smooth real lift with nonzero
lattice displacement. -/
theorem essential_smooth_torus_loop_has_nonzero_period (L : PeriodPair) (g : ℝ → PeriodTorus L)
    (hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ,ℂ) 1 g) (per : Function.Periodic g 1) (z : ℂ)
    (hz : periodTorusProjection L z=g 0) (γ : Path (periodTorusProjection L z) (periodTorusProjection L z))
    (loop : ∀ t : unitInterval, γ t=g t) (essential : FundamentalGroup.fromPath (.mk γ)≠1) :
    ∃ (ξ : ℝ → ℂ) (ω₀ : ℂ), ContDiff ℝ 1 ξ ∧ (∀ t, periodTorusProjection L (ξ t)=g t) ∧
      ω₀≠0 ∧ ω₀∈L.lattice ∧ ∀ t, ξ (t+1)=ξ t+ω₀ := by
  obtain ⟨ξ,sm,at0,pr⟩ := smooth_torus_curve_has_plane_lift L g hg z hz
  let ω₀ := ξ 1-ξ 0
  have lat : ω₀∈L.lattice := (periodTorusProjection_eq_iff L _ _).mp (by rw [pr,pr]; simpa using (per 0).symm)
  let period : L.lattice := ⟨ω₀,lat⟩
  have tip : ξ 1=z+ω₀ := by dsimp [ω₀]; rw [← at0]; abel
  let f : C(unitInterval,ℂ) := ⟨fun t => ξ t,sm.continuous.comp continuous_subtype_val⟩
  have classEq := periodTorusFundamentalGroupEquiv_of_lift L z γ f (funext fun t => (pr t).trans (loop t).symm) at0 period tip
  have nonz : ω₀≠0 := by
    intro h
    have eq : period=0 := Subtype.ext h
    rw [eq,map_zero] at classEq
    apply essential
    apply (periodTorusFundamentalGroupEquiv L z).injective
    rw [map_one]
    exact classEq
  refine ⟨ξ,ω₀,sm,pr,nonz,lat,?_⟩
  apply congrFun
  apply (periodTorusProjection_isCoveringMap L).eq_of_comp_eq
    (sm.continuous.comp (continuous_id.add continuous_const)) (sm.continuous.add continuous_const) _ (0:ℝ)
  · change ξ (0+1)=ξ 0+ω₀
    rw [zero_add,at0,tip]
  · funext t
    change periodTorusProjection L (ξ (t+1))=periodTorusProjection L (ξ t+ω₀)
    rw [periodTorusProjection_add_lattice L _ _ lat,pr,pr,per]

/-- A genuine essential regular plane section determines the even
quadratic form on the embedded torus. All plane-lift data and the
nonzero lattice increment follow from the actual section's loop class. -/
theorem embedded_torus_essential_horizontal_loop_even (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ)
    (embed : Function.Injective F) (sm : ∀ q≠0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (imm : ∀ q≠0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (g : ℝ → PeriodTorus L) (hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ,ℂ) 1 g) (per : Function.Periodic g 1)
    (z : ℂ) (hz : periodTorusProjection L z=g 0) (γ : Path (periodTorusProjection L z) (periodTorusProjection L z))
    (loop : ∀ t : unitInterval, γ t=g t) (essential : FundamentalGroup.fromPath (.mk γ)≠1)
    (away : ∀ t, g t≠0) (simple : ∀ t h : ℝ, h∈Ioo (0:ℝ) 1 → g (t+h)≠g t)
    (regular : ∀ t, deriv (F ∘ g) t≠0) {height : ℝ} (level : ∀ t, F (g t) 2=height)
    (transverse : ∀ t w, periodTorusProjection L w=g t → ∃ v, fderiv ℝ (F ∘ periodTorusProjection L) w v 2≠0) :
    ∀ v w, torusIntersectionModTwo v w=1 → capAmbientSpinQuadratic L F v*capAmbientSpinQuadratic L F w=0 := by
  obtain ⟨ξ,ω₀,hξ,pr,nz,lat,translation⟩ := essential_smooth_torus_loop_has_nonzero_period L g hg per z hz γ loop essential
  have off (t : ℝ) : ξ t∉L.lattice := fun h => away t ((pr t).symm.trans ((periodTorusProjection_eq_zero L _).mpr h))
  have form : (F ∘ periodTorusProjection L) ∘ ξ=F ∘ g := funext fun t => congrArg F (pr t)
  have reg (t : ℝ) : deriv ξ t≠0 := by
    intro h
    have s := (spatial_torus_lift_regular_at L F (off t) sm imm).1
    have d := (s.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t ((hξ.differentiable one_ne_zero t).hasDerivAt)
    rw [form,h,map_zero] at d
    exact regular t d.deriv
  have parity := embedded_torus_regular_plane_section_even L F embed sm imm hξ off nz lat translation reg
    (fun t d h => by simpa only [pr] using simple t d h) (fun t => by simpa only [pr] using level t)
    (fun t => transverse t _ (pr t))
  intro v w hw
  rw [cap_ambient_arf_basis L F v w hw]
  exact parity

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.essential_smooth_torus_loop_has_nonzero_period
#print axioms TwoAxisHelicoid.embedded_torus_essential_horizontal_loop_even
