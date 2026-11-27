import TwoAxisHelicoid.OriginalExteriorTorusReduction
import TwoAxisHelicoid.WeierstrassRotation

namespace TwoAxisHelicoid
open Bornology Complex Set Filter Topology InnerProductSpace
open scoped Topology Manifold ContDiff

theorem actual_holomorphic_chart_null {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (X : M → Fin 3 → ℝ) (hX : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) {z : ℂ} (hz : z ∈ e.target) :
    ComplexNull (immersionComplexCoefficient (X ∘ e.symm) z) := by
  let x := e.symm z
  let d := chartAt ℂ x
  let Y := X ∘ d.symm
  let u := d ∘ e.symm
  have hx : x ∈ d.source := mem_chart_source ℂ x
  obtain ⟨hh,hc,_⟩ := hX d (chart_mem_atlas ℂ x) _ (d.map_source hx)
  have hD : DifferentiableAt ℝ Y (u z) := (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hh j)).differentiableAt
  have htrans := (contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω)
    (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x)) hx).comp z (contMDiffAt_symm_of_mem_maximalAtlas he hz)
  have hu : AnalyticAt ℂ u z := htrans.contDiffAt.analyticAt
  have hloc : X ∘ e.symm =ᶠ[𝓝 z] Y ∘ u := by
    filter_upwards [(e.symm.continuousAt hz).eventually (d.open_source.mem_nhds hx)] with w hw
    exact congrArg X (d.left_inv hw).symm
  have hp := immersionComplexCoefficient_null hc
  have hψ (j : Fin 3) : immersionComplexCoefficient (X ∘ e.symm) z j = deriv u z * immersionComplexCoefficient Y (u z) j := by
    rw [← immersionComplexCoefficient_comp_holomorphic hD hu.differentiableAt.hasDerivAt]
    have he' : (fun w => (X ∘ e.symm) w j) =ᶠ[𝓝 z] (fun w => (Y ∘ u) w j) :=
      hloc.mono fun _ h => congrFun h j
    unfold immersionComplexCoefficient scalarComplexCoefficient
    rw [he'.fderiv_eq (𝕜 := ℝ)]
  unfold ComplexNull at hp ⊢
  change (immersionComplexCoefficient Y (u z) 0)^2+(immersionComplexCoefficient Y (u z) 1)^2+
    (immersionComplexCoefficient Y (u z) 2)^2=0 at hp
  rw [hψ,hψ,hψ]
  linear_combination (deriv u z)^2*hp

theorem geometric_exterior_coordinate_weierstrass {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (X : M → Fin 3 → ℝ) (hX : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    (A : GeometricExteriorCoordinate X) : ∀ᶠ z in cobounded ℂ,
    HasFDerivAt (X ∘ A.chart.symm)
      (nullRealDerivative (weierstrassTriple (exp (I*(A.pitch:ℂ)*z+A.correction z⁻¹)) 1)) z := by
  let e := A.chart
  let Y := X ∘ e.symm
  have hheight (z : ℂ) (hz : z ∈ e.target) : immersionComplexCoefficient Y z 2 = 1 := by
    have he : (fun w => Y w 2) =ᶠ[𝓝 z] (fun w : ℂ => A.heightOffset+w.re) := by
      filter_upwards [e.open_target.mem_nhds hz] with w hw
      exact (A.height _ (e.map_target hw)).trans (congrArg (fun u : ℂ => A.heightOffset+u.re) (e.right_inv hw))
    have h := scalarComplexCoefficient_of_real_part (hasDerivAt_id z) A.heightOffset
    unfold immersionComplexCoefficient scalarComplexCoefficient
    rw [he.fderiv_eq]
    exact h
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop A.radius),A.gauss] with z hz hg
  have hze : z ∈ e.target := A.target ▸ hz
  let p := immersionComplexCoefficient Y z
  have hp : ComplexNull p := actual_holomorphic_chart_null X hX A.holomorphic hze
  have h2 : p 2 = 1 := hheight _ hze
  obtain ⟨h0,h1⟩ := null_gauss_reconstruct hp (h2.trans_ne one_ne_zero)
  have hm : nullGauss p = exp (I*(A.pitch:ℂ)*z+A.correction z⁻¹) := hg
  have he : weierstrassTriple (exp (I*(A.pitch:ℂ)*z+A.correction z⁻¹)) 1 = p := by
    rw [← hm]
    ext j
    fin_cases j
    · change ((nullGauss p)⁻¹-nullGauss p)/2*1 = p 0
      simpa only [one_div,h2,mul_one] using h0
    · change I*((nullGauss p)⁻¹+nullGauss p)/2*1 = p 1
      simpa only [one_div,h2,mul_one] using h1
    · exact h2.symm
  rw [he]
  exact immersionComplexCoefficient_hasFDerivAt (differentiable_in_actual_holomorphic_chart X hX A.holomorphic hze)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.geometric_exterior_coordinate_weierstrass
