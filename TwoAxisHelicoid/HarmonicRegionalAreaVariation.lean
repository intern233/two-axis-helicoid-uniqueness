import TwoAxisHelicoid.HarmonicChartNormalAreaGeometry
import TwoAxisHelicoid.CompactSliceIntegralHessian

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Matrix Topology InnerProductSpace
open scoped ContDiff Manifold Topology

/-- The second derivative of the area of the actual spatial deformation,
measured on any given finite chart partition, equals the intrinsic energy.
The weight multiplies the area density, so there are no cutoff derivative
terms. The support of u may cross all the chart overlaps. -/
theorem partitioned_physical_second_area_variation {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {Ω : Set M} (op : IsOpen Ω) (P : CurveRegionPartition Ω)
    (X N : M → Fin 3 → ℝ) (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (normal : ∀ i z, z∈(P.chart i).target → N ((P.chart i).symm z)=harmonicChartNormal (X ∘ (P.chart i).symm) z)
    (u : M → ℝ) (smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ u) :
    HasDerivAt (deriv (fun s : ℝ => P.areaIntegral (fun i z =>
      coordinateAreaDensity ((fun p => X p+s • (u p • N p)) ∘ (P.chart i).symm) z))) (P.jacobiEnergy X u) 0 := by
  classical
  let density (i : P.indices) (s : ℝ) (z : ℂ) :=
    coordinateAreaDensity ((fun p => X p+s • (u p • N p)) ∘ (P.chart i).symm) z
  let w (i : P.indices) := P.weight i ∘ (P.chart i).symm
  let F (i : P.indices) (q : ℝ × ℂ) := w i q.2*density i q.1 q.2
  let K (i : P.indices) := P.chart i '' tsupport (P.weight i)
  let D (i : P.indices) := curveChartRegion (P.chart i) Ω
  let A (i : P.indices) := D i ∩ K i
  have support (i : P.indices) := (P.supported i).trans (P.patch i).carrier_subset_source
  have compact (i : P.indices) : IsCompact (K i) :=
    (P.compact i).image_of_continuousOn ((P.chart i).continuousOn.mono (support i))
  have inside (i : P.indices) : K i ⊆ (P.chart i).target := by
    rintro _ ⟨p,hp,rfl⟩
    exact (P.chart i).map_source (support i hp)
  have measurableD (i : P.indices) : MeasurableSet (D i) := (isOpen_curveChartRegion _ op).measurableSet
  have measurableA (i : P.indices) : MeasurableSet (A i) := (measurableD i).inter (compact i).measurableSet
  have restrictTo (i : P.indices) (f : ℂ → ℝ) :
      (∫ z in D i, w i z*f z) = ∫ z in A i, w i z*f z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableD i) inter_subset_left
    intro z hz
    have away : (P.chart i).symm z ∉ tsupport (P.weight i) := fun mem =>
      hz.2 ⟨hz.1,⟨_,mem,(P.chart i).right_inv hz.1.1⟩⟩
    exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport away) _
  have regular (i : P.indices) (z : ℂ) (hz : z ∈ K i) : ContDiffAt ℝ 2 (F i) (0,z) := by
    let e := P.chart i
    let Y := X ∘ e.symm
    have ez := inside i hz
    have r := harmonic_immersion_chart_maximal hX (P.member i) z ez
    have dy : AnalyticAt ℝ Y z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (r.1 j)
    have data := harmonicChartNormal_data dy r.2.1 r.2.2
    have dn : ContDiffAt ℝ ∞ (N ∘ e.symm) z := by
      apply data.1.contDiffAt.congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds ez] with p hp
      exact normal i p hp
    have positive : 0 < (planePartial 1 Y z ⬝ᵥ planePartial 1 Y z)*(planePartial I Y z ⬝ᵥ planePartial I Y z)
        -(planePartial 1 Y z ⬝ᵥ planePartial I Y z)^2 := by
      rw [← data.2.2.1,data.2.2.2.1]
      nlinarith [sq_pos_of_pos data.2.1]
    have gram := coordinate_normal_variation_density_smooth dy.contDiffAt dn (smooth_scalar_in_maximal_complex_chart smooth (P.member i) ez) positive
    exact (((smooth_scalar_in_maximal_complex_chart (P.smooth i) (P.member i) ez).of_le
      (show (2:ℕ∞ω) ≤ ∞ by simp)).comp (0,z) contDiffAt_snd).mul gram
  let J (i : P.indices) (s : ℝ) := ∫ z in A i, F i (s,z)
  have derivatives (i : P.indices) := compact_slice_integral_hessian (compact i) (measurableA i)
    (show A i ⊆ K i from inter_subset_right) (regular i)
  have sameArea : (fun s => P.areaIntegral (fun i z => density i s z)) = fun s => ∑ i, J i s :=
    funext fun s => Finset.sum_congr rfl fun i _ => restrictTo i (density i s)
  have sameEnergy : P.areaIntegral (fun i z => deriv (deriv (fun r => density i r z)) 0) =
      ∑ i, ∫ z in A i, deriv (deriv (fun r => F i (r,z))) 0 := by
    apply Finset.sum_congr rfl
    intro i _
    refine (restrictTo i (fun z => deriv (deriv (fun r => density i r z)) 0)).trans ?_
    apply setIntegral_congr_fun (measurableA i)
    intro z _
    simp only [F,deriv_const_mul_field',deriv_const_mul_field]
  have all : ∀ᶠ s in 𝓝 (0:ℝ), ∀ i : P.indices, DifferentiableAt ℝ (J i) s :=
    Filter.eventually_all.mpr (fun i => (derivatives i).1)
  have first : deriv (fun r : ℝ => ∑ i, J i r) =ᶠ[𝓝 0] fun r => ∑ i, deriv (J i) r :=
    all.mono (fun s hs => deriv_fun_sum fun i _ => hs i)
  change HasDerivAt (deriv (fun s => P.areaIntegral (fun i z => density i s z))) _ 0
  rw [sameArea,← partitioned_physical_pointwise_area_hessian op P X N hX normal u smooth]
  change HasDerivAt _ (P.areaIntegral (fun i z => deriv (deriv (fun r => density i r z)) 0)) 0
  rw [sameEnergy]
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (derivatives i).2)).congr_of_eventuallyEq first

/-- Use one globally defined oriented unit normal for all test functions,
regions and chart partitions. The equality of the chart normals follows
from the positive real Jacobian of holomorphic chart changes. -/
theorem harmonic_surface_regional_area_formula {M : Type*} [TopologicalSpace M] [T2Space M]
    [SigmaCompactSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    (X : M → Fin 3 → ℝ) (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) :
    ∃ N : M → Fin 3 → ℝ, (∀ p, N p ⬝ᵥ N p=1) ∧
      (∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target,
        N (e.symm z)=harmonicChartNormal (X ∘ e.symm) z) ∧
      ∀ Ω : Set M, IsOpen Ω → IsCompact (closure Ω) → HasSmoothCurveBoundary Ω →
        Nonempty (CurveRegionPartition Ω) ∧ ∀ (P : CurveRegionPartition Ω) (u : M → ℝ),
          ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ u →
            HasDerivAt (deriv (fun s : ℝ => P.areaIntegral (fun i z =>
              coordinateAreaDensity ((fun p => X p+s • (u p • N p)) ∘ (P.chart i).symm) z))) (P.jacobiEnergy X u) 0 := by
  let N (p : M) := harmonicChartNormal (X ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p)
  let normalized (v : Fin 3 → ℝ) := (Real.sqrt (v ⬝ᵥ v))⁻¹ • v
  have scale {k : ℝ} (pos : 0 < k) (v : Fin 3 → ℝ) : normalized (k • v)=normalized v := by
    dsimp only [normalized]
    rw [smul_dotProduct,dotProduct_smul]
    change (Real.sqrt (k*(k*(v ⬝ᵥ v))))⁻¹ • (k • v) = _
    rw [show k*(k*(v ⬝ᵥ v))=k^2*(v ⬝ᵥ v) by ring,Real.sqrt_mul (sq_nonneg k),
      Real.sqrt_sq pos.le,smul_smul,_root_.mul_inv_rev,mul_assoc,inv_mul_cancel₀ pos.ne',mul_one]
  have canonical (e : OpenPartialHomeomorph M ℂ) (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
      (z : ℂ) (hz : z∈e.target) :
      harmonicChartNormal (X ∘ e.symm) z=normalized (surfaceTangentCross (X ∘ e.symm) z) := by
    obtain ⟨h,c,i⟩ := harmonic_immersion_chart_maximal hX he z hz
    exact (harmonicChartNormal_data (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (h j)) c i).2.2.2.2.1
  have normal (e : OpenPartialHomeomorph M ℂ) (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
      (z : ℂ) (hz : z∈e.target) : N (e.symm z)=harmonicChartNormal (X ∘ e.symm) z := by
    let d := chartAt ℂ (e.symm z)
    let f := e.symm.trans d
    have hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := IsManifold.chart_mem_maximalAtlas _
    have src : z ∈ f.source := ⟨hz,mem_chart_source ℂ _⟩
    have target : f z ∈ d.target := d.map_source src.2
    have derivF := (complexAtlas_realized_transition he hd src).analyticAt.differentiableAt
    have nz : deriv f z ≠ 0 := holomorphic_transition_deriv_ne_zero he hd src
    have pos : 0 < planeRealJacobian (fderiv ℝ f z) := by
      rw [(derivF.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
      change 0 < (1*deriv f z).re*(I*deriv f z).im-(1*deriv f z).im*(I*deriv f z).re
      have positive := Complex.normSq_pos.mpr nz
      simp only [one_mul,Complex.I_mul_re,Complex.I_mul_im,Complex.normSq_apply] at positive ⊢
      linarith
    have same : X ∘ e.symm =ᶠ[𝓝 z] (X ∘ d.symm) ∘ f := by
      filter_upwards [f.open_source.mem_nhds src] with w hw
      exact congrArg X (d.left_inv hw.2).symm
    have harmon := (harmonic_immersion_chart_maximal hX hd _ target).1
    have diff : AnalyticAt ℝ (X ∘ d.symm) (f z) :=
      analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (harmon j)
    have cross := surfaceTangentCross_coordinate_change same diff.differentiableAt (derivF.restrictScalars ℝ)
    change harmonicChartNormal (X ∘ d.symm) (f z)=harmonicChartNormal (X ∘ e.symm) z
    rw [canonical d hd _ target,canonical e he z hz,cross,scale pos]
  refine ⟨N,?_,normal,?_⟩
  · intro p
    let e := chartAt ℂ p
    obtain ⟨h,c,i⟩ := hX e (chart_mem_atlas ℂ p) _ (e.map_source (mem_chart_source ℂ p))
    exact (harmonicChartNormal_data (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (h j)) c i).2.2.2.2.2.1
  · intro Ω opened compact boundary
    exact ⟨exists_curve_region_partition opened compact boundary,fun P u smooth =>
      partitioned_physical_second_area_variation opened P X N hX (fun i => normal _ (P.member i)) u smooth⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_chart_normal_area_hessian
#print axioms TwoAxisHelicoid.partitioned_physical_pointwise_area_hessian
#print axioms TwoAxisHelicoid.partitioned_physical_second_area_variation
#print axioms TwoAxisHelicoid.physical_normal_area_unchanged_off_support
#print axioms TwoAxisHelicoid.harmonic_surface_regional_area_formula
