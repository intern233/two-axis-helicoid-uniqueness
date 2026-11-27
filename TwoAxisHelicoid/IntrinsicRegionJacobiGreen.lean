import TwoAxisHelicoid.RegionFormIntegralIndependence
import TwoAxisHelicoid.RegularDefiningBoundaryStokes

namespace TwoAxisHelicoid
open Complex Set Filter Topology MeasureTheory Function
open scoped Topology Manifold ContDiff

/-- The exterior area in a single finite cover commutes with taking the
imaginary part. All localized densities are integrable on the region. -/
theorem CurveRegionPartition.imaginary_exterior_area {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {Ω : Set M} (P : CurveRegionPartition Ω) (a : P.indices → ℂ → ℂ)
    (c : ∀ i z, z∈(P.chart i).target → ContDiffAt ℝ 1 (a i) z) :
    P.areaIntegral (fun i z => (complexFormExteriorCoefficient (a i) z).im)=
      (∑ i, ∫ z in curveChartRegion (P.chart i) Ω, P.weight i ((P.chart i).symm z) •
        complexFormExteriorCoefficient (a i) z).im := by
  classical
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro i _
  have integ := (chart_weighted_density_integrable (P.chart i) (P.smooth i).continuous (P.compact i)
    ((P.supported i).trans (P.patch i).carrier_subset_source)
    (complexFormExteriorCoefficient_continuousOn (c i))).mono_set
    (show curveChartRegion (P.chart i) Ω⊆(P.chart i).target from inter_subset_left)
  simpa only [Function.comp_def,Complex.imCLM_apply,Complex.smul_im,smul_eq_mul] using Complex.imCLM.integral_comp_comm integ

/-- The integral with the outward unit conormal and the arclength of the
immersed boundary is independent of all localizations. No equation for
the fields is needed for this assertion. -/
theorem jacobi_boundary_flux_independent {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {Ω : Set M} (op : IsOpen Ω) (P Q : CurveRegionPartition Ω)
    (X : M → Fin 3 → ℝ) (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (u v : M → ℝ)
    (cu : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target, ContDiffAt ℝ 1 (u ∘ e.symm) z)
    (cv : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target, ContDiffAt ℝ 2 (v ∘ e.symm) z) :
    P.jacobiBoundaryFlux u v X=Q.jacobiBoundaryFlux u v X := by
  classical
  let a := fun (e : OpenPartialHomeomorph M ℂ) => jacobiBoundaryCoefficient (u ∘ e.symm) (v ∘ e.symm)
  have reg (e : OpenPartialHomeomorph M ℂ) (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
      (z : ℂ) (hz : z∈e.target) : ContDiffAt ℝ 1 (a e) z :=
    jacobi_boundary_coefficient_c1 (cu e he z hz) (cv e he z hz)
  have law (e : OpenPartialHomeomorph M ℂ) (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
      (d : OpenPartialHomeomorph M ℂ) (hd : d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
      (z : ℂ) (hz : z∈(e.symm.trans d).source) : a e z=a d ((e.symm.trans d) z)*deriv (e.symm.trans d) z := by
    let t := e.symm.trans d
    have same (f : M → ℝ) : f ∘ e.symm =ᶠ[𝓝 z] (f ∘ d.symm) ∘ t := by
      filter_upwards [t.open_source.mem_nhds hz] with w hw
      exact congrArg f (d.left_inv hw.2).symm
    exact jacobi_boundary_coefficient_chart_change
      (complexAtlas_realized_transition he hd hz).analyticAt.differentiableAt
      (same u).self_of_nhds (same v) ((cv d hd _ (d.map_source hz.2)).differentiableAt (by norm_num))
  have identify (S : CurveRegionPartition Ω) :
      (∑ i, ∫ z in curveChartRegion (S.chart i) Ω, S.weight i ((S.chart i).symm z) •
        complexFormExteriorCoefficient (a (S.chart i)) z).im=S.jacobiBoundaryFlux u v X := by
    have c i := reg (S.chart i) (S.member i)
    rw [← S.imaginary_exterior_area (fun i => a (S.chart i)) c,
      S.imaginary_stokes op _ c (fun i j => law _ (S.member i) _ (S.member j))]
    apply Finset.sum_congr rfl
    exact fun i _ => (S.patch i).flux_eq_jacobiFlux (S.weight i) u v (harmonic_immersion_chart_maximal hX (S.member i))
  exact (identify P).symm.trans ((congrArg Complex.im (region_exterior_integral_independent op P Q a reg law)).trans (identify Q))

/-- Intrinsic Appendix D.4. The same three numbers represent the two
fluxes and the energy in every finite chart partition of the smooth
physical region. This includes agreement of independently chosen covers. -/
theorem intrinsic_region_jacobi_green {M : Type*} [TopologicalSpace M] [T2Space M] [SigmaCompactSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {Ω : Set M} (op : IsOpen Ω)
    (compact : IsCompact (closure Ω)) (boundary : HasRegularDefiningBoundary Ω)
    (X : M → Fin 3 → ℝ) (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (u v : M → ℝ) (su : IsSurfaceJacobiField X u) (sv : IsSurfaceJacobiField X v) :
    Nonempty (CurveRegionPartition Ω) ∧ ∃ a b : ℝ, ∀ Q : CurveRegionPartition Ω,
      Q.jacobiBoundaryFlux u v X=a ∧ Q.jacobiBoundaryFlux v u X=a ∧
      Q.jacobiEnergy X u=b ∧ Q.jacobiBoundaryFlux u u X=b := by
  obtain ⟨existsP,allP⟩ := jacobi_green_on_regular_defining_regions op compact boundary X hX u v su sv
  refine ⟨existsP,?_⟩
  obtain ⟨P⟩ := existsP
  refine ⟨P.jacobiBoundaryFlux u v X,P.jacobiBoundaryFlux u u X,?_⟩
  intro Q
  have cU e he z hz := ((su e he z hz).1).of_le (show (1 : ℕ∞ω)≤2 by norm_num)
  have first := jacobi_boundary_flux_independent op Q P X hX u v cU (fun e he z hz => (sv e he z hz).1)
  have second := jacobi_boundary_flux_independent op Q P X hX u u cU (fun e he z hz => (su e he z hz).1)
  exact ⟨first,(sub_eq_zero.mp (allP Q).1).symm.trans first,(allP Q).2.trans second,second⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.intrinsic_region_jacobi_green
