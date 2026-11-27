import TwoAxisHelicoid.HarmonicRegionalAreaVariation
import TwoAxisHelicoid.CompactTestAreaHessian
import TwoAxisHelicoid.GeometricHelicoidHypotheses
import TwoAxisHelicoid.PuncturedTorusRealOrientation
import TwoAxisHelicoid.RealSurfaceIndexTransfer

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Matrix Topology InnerProductSpace
open scoped ContDiff Manifold Topology

universe u

/-- For every compactly supported test, construct its cover and its
second variation without selecting a region. Every other cover gives
the same full relative-area function and the same Jacobi integral. -/
theorem compactly_supported_surface_area_second_variation {M : Type u} [TopologicalSpace M] [T2Space M]
    [SigmaCompactSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    (X : M → Fin 3 → ℝ) (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) :
    ∃ N : M → Fin 3 → ℝ, (∀ p, N p ⬝ᵥ N p=1) ∧
      (∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target,
        N (e.symm z)=harmonicChartNormal (X ∘ e.symm) z) ∧
      ∀ v : M → ℝ, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ v → HasCompactSupport v →
        Nonempty (CompactTestChartCover (tsupport v)) ∧
        ∃! A : (ℝ → ℝ) × ℝ, HasDerivAt (deriv A.1) A.2 0 ∧
          ∀ P : CompactTestChartCover (tsupport v), P.relativeArea X N v=A.1 ∧ P.jacobiForm X v=A.2 := by
  classical
  obtain ⟨N,unit,normal,_⟩ := harmonic_surface_regional_area_formula X hX
  refine ⟨N,unit,normal,?_⟩
  intro v smooth compact
  obtain ⟨P⟩ := exists_compact_test_chart_cover compact
  have hp := compact_test_relative_area_hessian X N hX normal v smooth P
  refine ⟨⟨P⟩,⟨(P.relativeArea X N v,P.jacobiForm X v),⟨hp,?_⟩,?_⟩⟩
  · intro Q
    have same := compact_test_relative_area_independent X N hX normal v smooth Q P
    have hq := compact_test_relative_area_hessian X N hX normal v smooth Q
    rw [same] at hq
    exact ⟨same,hq.unique hp⟩
  · intro A hA
    exact Prod.ext (hA.2 P).1.symm (hA.2 P).2.symm

noncomputable def CurveRegionPartition.toCompactTestCover {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    {Ω K : Set M} (P : CurveRegionPartition Ω) (inside : K ⊆ Ω) : CompactTestChartCover K where
  indices := P.indices
  chart := P.chart
  member := P.member
  weight := P.weight
  unity := fun p hp => P.unity p (subset_closure (inside hp))
  smooth := P.smooth
  compact := P.compact
  supported := fun i => (P.supported i).trans (P.patch i).carrier_subset_source

/-- The intrinsic expression with the inverse metric, squared second
fundamental form and area factor on any region containing the support
equals the compact-support chart integral on the whole surface. -/
theorem regional_jacobi_energy_of_compact_test {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {Ω : Set M} (op : IsOpen Ω) (P : CurveRegionPartition Ω)
    (X : M → Fin 3 → ℝ) (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (v : M → ℝ) (inside : tsupport v ⊆ Ω) :
    P.jacobiEnergy X v=(P.toCompactTestCover inside).jacobiForm X v := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  let e := P.chart i
  let Y := X ∘ e.symm
  let V := v ∘ e.symm
  let g z := planePartial 1 Y z ⬝ᵥ planePartial 1 Y z
  let E z := planePartial 1 V z^2+planePartial I V z^2-jacobiPotentialDensity Y z*(V z)^2
  change (∫ z in curveChartRegion e Ω, P.weight i (e.symm z)*
    (((planePartial 1 V z^2+planePartial I V z^2)/g z-jacobiPotentialDensity Y z/g z*(V z)^2)*g z))=
    ∫ z in e.target, P.weight i (e.symm z)*E z
  calc
    _ = ∫ z in curveChartRegion e Ω, P.weight i (e.symm z)*E z := by
      apply setIntegral_congr_fun (isOpen_curveChartRegion e op).measurableSet
      intro z hz
      have germ : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun x => Y x j) w) ∧
          ConformalCoordinateDerivatives Y w ∧ Function.Injective (fderiv ℝ Y w) := by
        filter_upwards [e.open_target.mem_nhds hz.1] with w hw
        exact harmonic_immersion_chart_maximal hX (P.member i) w hw
      have pos : 0 < g z := (harmonic_chart_weingarten_frame germ).metric_pos
      dsimp only [E]
      field_simp [pos.ne']
    _ = _ := by
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e.open_target.measurableSet
        (show curveChartRegion e Ω ⊆ e.target from inter_subset_left)
      intro z hz
      have off : e.symm z ∉ tsupport v := fun hv => hz.2 ⟨hz.1,inside hv⟩
      have zero : V =ᶠ[𝓝 z] 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp off).comp_tendsto (e.symm.continuousAt hz.1).tendsto
      have d0 : fderiv ℝ V z=0 := by simpa using zero.fderiv_eq (𝕜 := ℝ)
      have v0 : V z=0 := zero.self_of_nhds
      simp [E,planePartial,d0,v0]

/-- The induced conformal structure supplies the charts, while the
test vector is smooth in the original real surface structure. Only
the smooth immersed minimal punctured torus and its closed embedding
from the original surface data are used. -/
theorem original_surface_compact_area_second_variation (surface : OriginalSmoothHelicoid) :
    let smoothTest := fun v : surface.carrier → ℝ => ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ v
    ∃ S : ChartedSpace ℂ surface.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω surface.carrier ∧
      (∀ e∈atlas ℂ surface.carrier, HarmonicImmersionChart surface.position e) ∧
      ∃ N : surface.carrier → Fin 3 → ℝ, (∀ p, N p ⬝ᵥ N p=1) ∧
        (∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω surface.carrier, ∀ z∈e.target,
          N (e.symm z)=harmonicChartNormal (surface.position ∘ e.symm) z) ∧
        ∀ v : surface.carrier → ℝ, smoothTest v → HasCompactSupport v →
          Nonempty (CompactTestChartCover (tsupport v)) ∧
          ∃! A : (ℝ → ℝ) × ℝ, HasDerivAt (deriv A.1) A.2 0 ∧
            ∀ P : CompactTestChartCover (tsupport v),
              P.relativeArea surface.position N v=A.1 ∧ P.jacobiForm surface.position v=A.2 := by
  let old := smooth_surface_regular_manifold_chart surface.smooth surface.immersion
  let : SigmaCompactSpace surface.carrier := surface.closedEmbedding.sigmaCompactSpace
  obtain ⟨S,man,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas
    surface.topologicalType surface.smooth surface.immersion surface.minimal
  refine ⟨S,man,charts,?_⟩
  let _ := S
  let _ := man
  let _ := complex_curve_underlying_real_manifold surface.carrier
  have reg (p : surface.carrier) : RegularImmersionChart surface.position (S.chartAt p) := by
    intro z hz
    obtain ⟨harm,_,imm⟩ := charts (S.chartAt p) (S.chart_mem_atlas p) z hz
    exact ⟨(analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (harm j))).contDiffAt,imm⟩
  obtain ⟨N,unit,normal,main⟩ := compactly_supported_surface_area_second_variation surface.position charts
  exact ⟨N,unit,normal,fun v smooth compact => main v
    (smooth_in_original_regular_spatial_atlas (orig := S) reg surface.charts old v smooth) compact⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_chart_normal_area_hessian
#print axioms TwoAxisHelicoid.partitioned_physical_pointwise_area_hessian
#print axioms TwoAxisHelicoid.partitioned_physical_second_area_variation
#print axioms TwoAxisHelicoid.physical_normal_area_unchanged_off_support
#print axioms TwoAxisHelicoid.harmonic_surface_regional_area_formula
#print axioms TwoAxisHelicoid.compact_test_relative_area_independent
#print axioms TwoAxisHelicoid.compact_test_relative_area_hessian
#print axioms TwoAxisHelicoid.compactly_supported_surface_area_second_variation
#print axioms TwoAxisHelicoid.compact_test_jacobi_form_intrinsic
#print axioms TwoAxisHelicoid.regional_jacobi_energy_of_compact_test
#print axioms TwoAxisHelicoid.original_surface_compact_area_second_variation
