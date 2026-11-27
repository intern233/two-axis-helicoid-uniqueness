import TwoAxisHelicoid.SmoothRegionStokes
import TwoAxisHelicoid.JacobiComplexBoundaryForm
import TwoAxisHelicoid.HarmonicChartGreenIdentities
import TwoAxisHelicoid.MaximalHarmonicImmersionChart

namespace TwoAxisHelicoid
open Complex Set Filter Topology MeasureTheory Function Matrix InnerProductSpace Laplacian
open scoped Topology Manifold ContDiff Interval

/-- Outward conormal flux in an actual oriented boundary chart,
including the Euclidean arclength density of the immersed boundary. -/
noncomputable def CurveRegionPatch.jacobiFlux {M : Type*} [TopologicalSpace M] {Ω : Set M}
    {e : OpenPartialHomeomorph M ℂ} (P : CurveRegionPatch e Ω) (ρ u v : M → ℝ) (X : M → Fin 3 → ℝ) : ℝ :=
  match P with
  | .interior => 0
  | .boundary G => ∫ x in G.l..G.r,
      let z := Complex.equivRealProdCLM.symm (x,G.φ x)
      let w : ℂ := ⟨1,deriv G.φ x⟩
      let D := fderiv ℝ (coordinateToEuclidean ∘ X ∘ e.symm) z
      ρ (e.symm z)*(‖D w‖*(u (e.symm z)*fderiv ℝ (v ∘ e.symm) z (‖D (-I*w)‖⁻¹ • (-I*w))))

/-- Convert the flux of the complex form into the geometric conormal
of the immersed graph. The speed is nonzero by chart regularity. -/
theorem CurveRegionPatch.flux_eq_jacobiFlux {M : Type*} [TopologicalSpace M] {Ω : Set M}
    {e : OpenPartialHomeomorph M ℂ} (P : CurveRegionPatch e Ω) (ρ u v : M → ℝ) {X : M → Fin 3 → ℝ}
    (regular : HarmonicImmersionChart X e) :
    P.flux (fun w => (ρ (e.symm w):ℂ)*jacobiBoundaryCoefficient (u ∘ e.symm) (v ∘ e.symm) w)=
      P.jacobiFlux ρ u v X := by
  cases P with
  | interior => rfl
  | boundary G =>
    apply intervalIntegral.integral_congr
    intro x hx
    let z := Complex.equivRealProdCLM.symm (x,G.φ x)
    let w : ℂ := ⟨1,deriv G.φ x⟩
    have hit : z∈e.target := G.boundary x (by simpa only [uIcc_of_le G.ordered] using hx)
    obtain ⟨harm,conformal,inj⟩ := regular z hit
    have diff : DifferentiableAt ℝ (X ∘ e.symm) z :=
      (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (harm j)).differentiableAt
    have nonzero : w≠0 := fun eq => one_ne_zero (congrArg Complex.re eq)
    have speed : fderiv ℝ (coordinateToEuclidean ∘ X ∘ e.symm) z w≠0 := by
      rw [(coordinateToEuclidean.hasFDerivAt.comp z diff.hasFDerivAt).fderiv]
      intro eq
      have raw : (fderiv ℝ (X ∘ e.symm) z) w=0 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective
        (eq.trans (map_zero coordinateToEuclidean).symm)
      exact nonzero (inj (raw.trans (map_zero _).symm))
    have flux := jacobi_boundary_form_physical_flux (w:=w) (immersionComplexCoefficient_null conformal)
      (immersionComplexCoefficient_hasFDerivAt diff) speed (u ∘ e.symm) (v ∘ e.symm)
    change (w*((ρ (e.symm z):ℂ)*jacobiBoundaryCoefficient (u ∘ e.symm) (v ∘ e.symm) z)).im=_
    rw [← mul_assoc w,mul_comm w (ρ (e.symm z):ℂ),mul_assoc,Complex.im_ofReal_mul]
    exact congrArg (fun value : ℝ => ρ (e.symm z)*value) flux.symm

noncomputable def CurveRegionPartition.jacobiBoundaryFlux {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {Ω : Set M} (P : CurveRegionPartition Ω) (u v : M → ℝ) (X : M → Fin 3 → ℝ) : ℝ :=
  ∑ i, (P.patch i).jacobiFlux (P.weight i) u v X

/-- Green's first identity for two scalar fields in any actual
conformal chart cover, one field satisfying the intrinsic Jacobi
equation. The boundary is integrated using the physical conormal. -/
theorem surface_region_jacobi_green {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {Ω : Set M} (op : IsOpen Ω) (P : CurveRegionPartition Ω) (X : M → Fin 3 → ℝ) (u v : M → ℝ)
    (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (cu : ∀ i z, z∈(P.chart i).target → ContDiffAt ℝ 1 (u ∘ (P.chart i).symm) z)
    (cv : ∀ i z, z∈(P.chart i).target → ContDiffAt ℝ 2 (v ∘ (P.chart i).symm) z)
    (sol : ∀ i z, z∈(P.chart i).target →
      conformalSurfaceJacobi (X ∘ (P.chart i).symm) (v ∘ (P.chart i).symm) z=0) :
    P.areaIntegral (fun i z =>
      let U := u ∘ (P.chart i).symm
      let V := v ∘ (P.chart i).symm
      planePartial 1 U z*planePartial 1 V z+planePartial I U z*planePartial I V z-
        jacobiPotentialDensity (X ∘ (P.chart i).symm) z*U z*V z)=P.jacobiBoundaryFlux u v X := by
  classical
  let A := fun i => jacobiBoundaryCoefficient (u ∘ (P.chart i).symm) (v ∘ (P.chart i).symm)
  have reg i := harmonic_immersion_chart_maximal hX (P.member i)
  have chartLaw (i j : P.indices) (z : ℂ) (hz : z∈((P.chart i).symm.trans (P.chart j)).source) :
      A i z=A j (((P.chart i).symm.trans (P.chart j)) z)*deriv ((P.chart i).symm.trans (P.chart j)) z := by
    let t := (P.chart i).symm.trans (P.chart j)
    have same (f : M → ℝ) : f ∘ (P.chart i).symm =ᶠ[𝓝 z] (f ∘ (P.chart j).symm) ∘ t := by
      filter_upwards [t.open_source.mem_nhds hz] with w hw
      exact congrArg f ((P.chart j).left_inv hw.2).symm
    exact jacobi_boundary_coefficient_chart_change
      (complexAtlas_realized_transition (P.member i) (P.member j) hz).analyticAt.differentiableAt
      (same u).self_of_nhds (same v)
      ((cv j _ ((P.chart j).map_source hz.2)).differentiableAt (by norm_num))
  have stokes := P.imaginary_stokes op A (fun i z hz => jacobi_boundary_coefficient_c1 (cu i z hz) (cv i z hz)) chartLaw
  calc
    _=P.areaIntegral (fun i z => (complexFormExteriorCoefficient (A i) z).im) := by
      apply Finset.sum_congr rfl
      intro i _
      apply setIntegral_congr_fun (isOpen_curveChartRegion (P.chart i) op).measurableSet
      intro z hz
      exact congrArg (fun value : ℝ => P.weight i ((P.chart i).symm z)*value)
        (imaginary_jacobi_exterior (cu i z hz.1) (cv i z hz.1)
          (regular_jacobi_equation_density (reg i z hz.1).2.2 (sol i z hz.1))).symm
    _=P.boundaryIntegral A := stokes
    _=P.jacobiBoundaryFlux u v X := by
      apply Finset.sum_congr rfl
      exact fun i _ => (P.patch i).flux_eq_jacobiFlux (P.weight i) u v (reg i)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CurveRegionPatch.flux_eq_jacobiFlux
#print axioms TwoAxisHelicoid.surface_region_jacobi_green

