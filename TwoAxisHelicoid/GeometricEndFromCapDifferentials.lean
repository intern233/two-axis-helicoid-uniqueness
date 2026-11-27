import TwoAxisHelicoid.PuncturedHeightInverseExterior
import TwoAxisHelicoid.OriginalPoleEndTorusReduction
import TwoAxisHelicoid.MaximalHarmonicImmersionChart

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric Bornology MeasureTheory
open scoped Topology ContDiff Manifold

/-- In the original puncture chart the two pole orders, vanishing
peripheral height periods, and the regular logarithmic remainder produce
a genuine normalized geometric exterior on the physical surface. -/
theorem geometric_exterior_of_cap_differentials {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ}
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d) (A : GeometricDoublePoleEnd X) {α : ℝ}
    (period : ∀ R : ℝ, 0<R → ∃ r∈Ioo (0:ℝ) R,
      (∮ z in C(0,r), immersionComplexCoefficient (X ∘ A.endChart.coord.symm) z 2)=0)
    (remainder : ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ ∀ᶠ w in 𝓝[≠] (0:ℂ),
      immersionGaussLogDerivative (X ∘ A.endChart.coord.symm) w-
      I*(α:ℂ)*immersionComplexCoefficient (X ∘ A.endChart.coord.symm) w 2=Q w) :
    ∃ G : GeometricExteriorCoordinate X, G.pitch=α ∧ G.correction 0=0 := by
  let E := A.endChart
  let Y := X ∘ E.coord.symm
  let x := fun z => Y z 2
  let h := fun z => immersionComplexCoefficient Y z 2
  let g := immersionGaussMap Y
  have chart := harmonic_immersion_chart_maximal charts A.holomorphic
  have domain : ∀ᶠ w in 𝓝[≠] (0:ℂ), w∈E.coord.target := by
    change E.coord.target∈𝓝[≠] (0:ℂ)
    rw [E.target_eq]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ E.radius_pos)) self_mem_nhdsWithin
  have reg : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ x w ∧ scalarComplexCoefficient x w=h w := by
    filter_upwards [domain] with w hw
    exact ⟨(_root_.HarmonicAt.analyticAt ((chart w hw).1 2)).differentiableAt,rfl⟩
  have mer : MeromorphicAt (logDeriv g) 0 := A.gauss
  have order : meromorphicOrderAt (logDeriv g) 0=(-2:ℤ) := A.gaussOrder
  obtain ⟨u,hu,nu,fac⟩ := (meromorphicOrderAt_eq_int_iff mer).mp order
  obtain ⟨Q,qa,eq⟩ := remainder
  have gauss : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ g w ∧ g w≠0 ∧ logDeriv g w-I*(α:ℂ)*h w=Q w := by
    filter_upwards [fac,(hu.continuousAt.eventually_ne nu).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin,eq] with w hw unit ne he
    change w≠0 at ne
    have val : logDeriv g w=u w/w^2 := by simpa [sub_zero,smul_eq_mul,zpow_neg,div_eq_mul_inv,mul_comm] using hw
    have non := val.trans_ne (div_ne_zero unit (pow_ne_zero _ ne))
    refine ⟨?_,fun zero => non (by simp [logDeriv_apply,zero]),he⟩
    by_contra nd
    exact non (by simp [logDeriv_apply,deriv_zero_of_not_differentiableAt nd])
  obtain ⟨pitch,H,k,F,b,ka,k0,fa,f0,near,lim,far⟩ :=
    original_cap_differentials_give_height_normal_form A.height A.heightOrder period reg order qa gauss
  obtain ⟨r,rp,sub⟩ := Metric.mem_nhdsWithin_iff.mp near
  let W := ball (0:ℂ) r \ {0}
  have op : IsOpen W := isOpen_ball.sdiff isClosed_singleton
  have Wmem : ∀ᶠ w in 𝓝[≠] (0:ℂ), w∈W := inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ rp)) self_mem_nhdsWithin
  have an : AnalyticOnNhd ℂ H W := (show DifferentiableOn ℂ H W from
    fun w hw => (sub hw).1.differentiableAt.differentiableWithinAt).analyticOnNhd op
  obtain ⟨d,R,Rp,target,source,small,_,dw,dξ,ad,ai⟩ := punctured_height_exterior_chart ka k0 lim
    ((Wmem.and near).mono fun w hw => ⟨an w hw.1,hw.2.2.1⟩) (far.mono fun _ h => h.1)
    (domain.and (near.mono fun _ h => h.2.2)) (univ_mem (f := cobounded ℂ))
  let e := E.coord.trans d
  have tar : e.target={ξ : ℂ | R<‖ξ‖} := by
    rw [← target]
    ext ξ
    change (ξ∈d.target ∧ d.symm ξ∈E.coord.target) ↔ ξ∈d.target
    exact ⟨And.left,fun hx => ⟨hx,(small (d.map_target hx)).1⟩⟩
  have old : ∀ᶠ z in cocompact M, z∈E.coord.source := by
    change E.coord.source∈cocompact M
    simpa only [compl_compl] using E.compact_core.compl_mem_cocompact
  have toP : Tendsto E.coord (cocompact M) (𝓝[≠] (0:ℂ)) := tendsto_nhdsWithin_iff.mpr
    ⟨E.to_zero,old.mono fun _ hx => E.coord_ne_zero hx⟩
  have reaches : e.source∈cocompact M := old.and (toP.eventually source)
  obtain ⟨C,compact,inc⟩ := mem_cocompact.mp reaches
  have core : IsCompact e.sourceᶜ := compact.of_isClosed_subset e.open_source.isClosed_compl
    (fun z hz => by by_contra h; exact hz (inc h))
  have hol : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
    apply e.mem_maximalAtlas_of_contMDiffOn
    · intro z hz
      have sm : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω d (E.coord z) :=
        contMDiffAt_iff_contDiffAt.mpr (ad _ hz.2).contDiffAt
      exact (sm.comp z (contMDiffAt_of_mem_maximalAtlas A.holomorphic hz.1)).contMDiffWithinAt
    · intro ξ hξ
      have sm : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω d.symm ξ :=
        contMDiffAt_iff_contDiffAt.mpr (ai _ hξ.1).contDiffAt
      exact ((contMDiffAt_symm_of_mem_maximalAtlas A.holomorphic hξ.2).comp ξ sm).contMDiffWithinAt
  refine ⟨⟨e,R,Rp,tar,core,hol,b,?_,α,pitch,F,fa,?_⟩,rfl,f0⟩
  · intro z hz
    have height := (small hz.2).2
    change X (E.coord.symm (E.coord z)) 2=b+(H (E.coord z)).re at height
    change X z 2=b+(d (E.coord z)).re
    rwa [E.coord.left_inv hz.1,← dw] at height
  · have tail : d.target∈cobounded ℂ := by
      rw [target]
      filter_upwards [eventually_cobounded_le_norm (E := ℂ) (R+1)] with ξ h
      linarith
    filter_upwards [tail,far] with ξ hξ expform
    have hz := d.map_target hξ
    have dy : DifferentiableAt ℝ Y (d.symm ξ) :=
      (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((chart _ (small hz).1).1 j))).differentiableAt
    have comp : d ∘ d.symm =ᶠ[𝓝 ξ] id := by
      filter_upwards [d.open_target.mem_nhds hξ] with w hw
      exact d.right_inv hw
    have prod := (deriv_comp ξ (ad _ hz).differentiableAt (ai _ hξ).differentiableAt).symm.trans
      (comp.deriv_eq.trans (deriv_id ξ))
    have non : deriv d.symm ξ≠0 := fun zero => by simp [zero] at prod
    exact (immersionGaussMap_comp_holomorphic dy (ai _ hξ).differentiableAt.hasDerivAt non).trans
      ((dξ ξ) ▸ expform.2.2)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.geometric_exterior_of_cap_differentials
