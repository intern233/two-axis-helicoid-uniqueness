import TwoAxisHelicoid.AntiholomorphicChartGerms
import TwoAxisHelicoid.SpatialAxisGermDifferentials
import TwoAxisHelicoid.SymmetricCapPrincipalParts

namespace TwoAxisHelicoid
open Complex Set Filter Metric InnerProductSpace
open scoped Topology ComplexConjugate ContDiff Manifold

/-- The two half-turn equations on the actual spatial immersion near
its puncture determine the real pitch and the complete normalized
exterior chart. No residue, Gauss transformation, periodic primitive,
or global uniformization is specified. -/
theorem geometric_exterior_of_reflected_spatial_cap {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ}
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d) (A : GeometricDoublePoleEnd X)
    (u v : ℂ → ℂ) (au : AnalyticAt ℂ u 0) (u0 : u 0=0) (un : deriv u 0≠0)
    (av : AnalyticAt ℂ v 0) (v0 : v 0=0) (vn : deriv v 0≠0) :
    let Y := X ∘ A.endChart.coord.symm
    ((Y ∘ u) =ᶠ[𝓝[≠] (0:ℂ)] (halfTurnX ∘ halfTurnZ ∘ Y)) →
    ((Y ∘ v) =ᶠ[𝓝[≠] (0:ℂ)] (halfTurnX ∘ Y ∘ conj)) →
    ∃ G : GeometricExteriorCoordinate X, G.pitch≠0 ∧ G.correction 0=0 := by
  intro Y product horizontal
  let h := fun z => immersionComplexCoefficient Y z 2
  let g := immersionGaussMap Y
  let k := logDeriv g
  have tu : Tendsto u (𝓝[≠] (0:ℂ)) (𝓝[≠] 0) := by simpa only [u0] using au.differentiableAt.hasDerivAt.tendsto_nhdsNE un
  have tv : Tendsto v (𝓝[≠] (0:ℂ)) (𝓝[≠] 0) := by simpa only [v0] using av.differentiableAt.hasDerivAt.tendsto_nhdsNE vn
  have tc := conjugation_tendsto_punctured_origin
  have chart := harmonic_immersion_chart_maximal charts A.holomorphic
  have domain : A.endChart.coord.target∈𝓝[≠] (0:ℂ) := by
    rw [A.endChart.target_eq]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ A.endChart.radius_pos)) self_mem_nhdsWithin
  have reg : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ Y z ∧ ComplexNull (immersionComplexCoefficient Y z) ∧
      h z≠0 ∧ DifferentiableAt ℂ g z ∧ g z≠0 := by
    have hne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero A.height).mp (by rw [A.heightOrder]; norm_num)
    have kne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero A.gauss).mp (by rw [A.gaussOrder]; norm_num)
    filter_upwards [domain,hne,kne] with z hz hn kn
    have kn' : logDeriv g z≠0 := kn
    refine ⟨(analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((chart z hz).1 j))).differentiableAt,
      immersionComplexCoefficient_null (chart z hz).2.1,hn,?_,fun zero => kn' (by simp [logDeriv_apply,zero])⟩
    by_contra nd
    exact kn' (by simp [logDeriv_apply,deriv_zero_of_not_differentiableAt nd])
  have up : ∀ᶠ z in 𝓝[≠] (0:ℂ), deriv u z*h (u z)= -h z ∧ g (u z)*g z= -1 := by
    filter_upwards [reg,tu.eventually reg,au.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (au.deriv.continuousAt.eventually_ne un).filter_mono nhdsWithin_le_nhds,punctured_germ_eventually_local product]
      with z rz ru a n e using physical_axis_product_germ rz.1 ru.1 a.differentiableAt n rz.2.1 rz.2.2.1 e
  have vp : ∀ᶠ z in 𝓝[≠] (0:ℂ), deriv v z*h (v z)= -conj (h (conj z)) ∧ g (v z)= -conj (g (conj z)) := by
    filter_upwards [tc.eventually reg,tv.eventually reg,av.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      (av.deriv.continuousAt.eventually_ne vn).filter_mono nhdsWithin_le_nhds,punctured_germ_eventually_local horizontal]
      with z rc rv a n e using physical_horizontal_reflection_germ rc.1 rv.1 a.differentiableAt n e
  have inv : (g ∘ u) =ᶠ[𝓝[≠] (0:ℂ)] (fun z => -1/g z) := by
    filter_upwards [up,reg] with z e r using (eq_div_iff r.2.2.2.2).mpr e.2
  have ku : ∀ᶠ z in 𝓝[≠] (0:ℂ), deriv u z*k (u z)= -k z := by
    filter_upwards [logDeriv_congr_nhdsNE inv,reg,tu.eventually reg,au.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with z e rz ru an
    change logDeriv (g ∘ u) z=logDeriv ((fun _ : ℂ => (-1:ℂ))/g) z at e
    rw [logDeriv_comp ru.2.2.2.1 an.differentiableAt,
      logDeriv_div (f := fun _ : ℂ => (-1:ℂ)) z (by norm_num) rz.2.2.2.2 (differentiableAt_const (-1:ℂ)) rz.2.2.2.1,logDeriv_const,Pi.zero_apply,zero_sub] at e
    simpa only [k,mul_comm] using e
  have cv : (g ∘ v) =ᶠ[𝓝[≠] (0:ℂ)] fun z => -((conj ∘ g ∘ conj) z) := vp.mono (fun _ e => e.2)
  have kv : ∀ᶠ z in 𝓝[≠] (0:ℂ), deriv v z*k (v z)=conj (k (conj z)) := by
    filter_upwards [logDeriv_congr_nhdsNE cv,tc.eventually reg,tv.eventually reg,av.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with z e rc rv an
    rw [logDeriv_comp rv.2.2.2.1 an.differentiableAt,logDeriv_neg] at e
    have d := rc.2.2.2.1.hasDerivAt.conj_conj
    simp only [starRingEnd_self_apply] at d
    change deriv v z*logDeriv g (v z)=_
    have derivEq : deriv (conj ∘ g ∘ conj) z=conj (deriv g (conj z)) := d.deriv
    simpa only [k,logDeriv_apply,derivEq,Function.comp_apply,map_div₀,mul_comm] using e
  apply geometric_exterior_of_symmetric_cap_poles charts A u (v ∘ conj) au u0 un (up.mono (fun _ e => e.1)) ku (tv.comp tc)
  have rv : ∀ᶠ z in 𝓝[≠] (0:ℂ), k (v z)/h (v z)= -conj (k (conj z)/h (conj z)) := by
    filter_upwards [vp,kv,(av.deriv.continuousAt.eventually_ne vn).filter_mono nhdsWithin_le_nhds] with z hv e n
    rw [← mul_div_mul_left (k (v z)) (h (v z)) n,e,hv.1,map_div₀,div_neg]
  change ∀ᶠ z in 𝓝[≠] (0:ℂ), k (v (conj z))/h (v (conj z))= -conj (k z/h z)
  simpa only [starRingEnd_self_apply] using tc.eventually rv

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.geometric_exterior_of_reflected_spatial_cap
