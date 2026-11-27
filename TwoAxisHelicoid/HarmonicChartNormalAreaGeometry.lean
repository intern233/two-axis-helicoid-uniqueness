import TwoAxisHelicoid.HarmonicNormalAreaDensity
import TwoAxisHelicoid.SmoothRegionGreenIdentities
import TwoAxisHelicoid.IsothermalComplexAtlas
import TwoAxisHelicoid.SmoothMarkedCircleClass
import TwoAxisHelicoid.MaximalHarmonicImmersionChart

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Matrix Topology InnerProductSpace
open scoped ContDiff Manifold Topology

theorem harmonic_chart_normal_area_hessian {Y : ℂ → Fin 3 → ℝ} {u : ℂ → ℝ} {z : ℂ}
    (h : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun x => Y x j) w) ∧
      ConformalCoordinateDerivatives Y w ∧ Function.Injective (fderiv ℝ Y w))
    (du : DifferentiableAt ℝ u z) :
    HasDerivAt (deriv (fun s : ℝ => coordinateAreaDensity
      (fun w => Y w+s • (u w • harmonicChartNormal Y w)) z))
      (planePartial 1 u z^2+planePartial I u z^2-jacobiPotentialDensity Y z*(u z)^2) 0 :=
  coordinateAreaDensity_harmonic_normal_hessian h du

theorem smooth_scalar_in_maximal_complex_chart {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {u : M → ℝ} (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ u)
    {e : OpenPartialHomeomorph M ℂ} (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    {z : ℂ} (hz : z∈e.target) : ContDiffAt ℝ ∞ (u ∘ e.symm) z := by
  let _ := complex_curve_underlying_real_manifold M
  let c := chartAt ℂ (e.symm z)
  let t := e.symm.trans c
  have hit : z∈t.source := ⟨hz,mem_chart_source ℂ _⟩
  have transition := complexAtlas_realized_transition he (IsManifold.chart_mem_maximalAtlas _) hit
  have hol : ContDiffAt ℝ ∞ t z := (transition.restrict_scalars ℝ).of_le (by simp)
  have inv : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm (t z) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _) (c.map_source hit.2)
  apply ((sm.contMDiffAt.comp (t z) inv).contDiffAt.comp z hol).congr_of_eventuallyEq
  filter_upwards [t.open_source.mem_nhds hit] with w hw
  exact congrArg u (c.left_inv hw.2).symm

/-- Finite integration of the pointwise physical Hessian, using the
same global displacement s u N in every chart. No Jacobi equation or
single-chart support is imposed on the test function. -/
theorem partitioned_physical_pointwise_area_hessian {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {Ω : Set M} (op : IsOpen Ω) (P : CurveRegionPartition Ω)
    (X N : M → Fin 3 → ℝ) (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (normal : ∀ i z, z∈(P.chart i).target → N ((P.chart i).symm z)=harmonicChartNormal (X ∘ (P.chart i).symm) z)
    (u : M → ℝ) (smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ u) :
    P.areaIntegral (fun i z => deriv (deriv (fun s : ℝ => coordinateAreaDensity
      ((fun p => X p+s • (u p • N p)) ∘ (P.chart i).symm) z)) 0)=P.jacobiEnergy X u := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun (isOpen_curveChartRegion (P.chart i) op).measurableSet
  intro z hz
  let e := P.chart i
  let Y := X ∘ e.symm
  let U := u ∘ e.symm
  have loc := harmonic_immersion_chart_maximal hX (P.member i)
  have germ : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun x => Y x j) w) ∧
      ConformalCoordinateDerivatives Y w ∧ Function.Injective (fderiv ℝ Y w) := by
    filter_upwards [e.open_target.mem_nhds hz.1] with w hw
    exact loc w hw
  have regular := harmonic_chart_weingarten_frame germ
  have sm := smooth_scalar_in_maximal_complex_chart smooth (P.member i) hz.1
  have val := (harmonic_chart_normal_area_hessian germ (sm.differentiableAt (by simp))).deriv
  have same : (fun s : ℝ => coordinateAreaDensity ((fun p => X p+s • (u p • N p)) ∘ e.symm) z)=
      fun s => coordinateAreaDensity (fun w => Y w+s • (U w • harmonicChartNormal Y w)) z := by
    funext s
    apply coordinateAreaDensity_congr_local
    filter_upwards [e.open_target.mem_nhds hz.1] with w hw
    change X (e.symm w)+s • (u (e.symm w) • N (e.symm w)) =
      X (e.symm w)+s • (u (e.symm w) • harmonicChartNormal Y w)
    exact congrArg (fun n => X (e.symm w)+s • (u (e.symm w) • n)) (normal i w hw)
  change P.weight i (e.symm z) * deriv (deriv (fun s : ℝ =>
    coordinateAreaDensity ((fun p => X p+s • (u p • N p)) ∘ e.symm) z)) 0 = P.weight i (e.symm z) *
    (((planePartial 1 U z^2+planePartial I U z^2)/(planePartial 1 Y z ⬝ᵥ planePartial 1 Y z)-
      jacobiPotentialDensity Y z/(planePartial 1 Y z ⬝ᵥ planePartial 1 Y z)*U z^2)*(planePartial 1 Y z ⬝ᵥ planePartial 1 Y z))
  rw [same]
  have result : deriv (deriv (fun s : ℝ =>
      coordinateAreaDensity (fun w => Y w+s • (U w • harmonicChartNormal Y w)) z)) 0 =
      planePartial 1 U z^2 + planePartial I U z^2 - jacobiPotentialDensity Y z * U z^2 := val
  rw [result]
  field_simp [regular.metric_pos.ne']

theorem coordinate_normal_variation_density_smooth {Y N : ℂ → Fin 3 → ℝ} {u : ℂ → ℝ} {z : ℂ}
    (dy : ContDiffAt ℝ ∞ Y z) (dn : ContDiffAt ℝ ∞ N z) (du : ContDiffAt ℝ ∞ u z)
    (positive : 0 < (planePartial 1 Y z ⬝ᵥ planePartial 1 Y z)*(planePartial I Y z ⬝ᵥ planePartial I Y z)
      -(planePartial 1 Y z ⬝ᵥ planePartial I Y z)^2) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℂ => coordinateAreaDensity (fun w => Y w+q.1 • (u w • N w)) q.2) (0,z) := by
  let T := fun (v : ℂ) (q : ℝ × ℂ) => planePartial v Y q.2+
    q.1 • (planePartial v u q.2 • N q.2+u q.2 • planePartial v N q.2)
  have psm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℂ → E}
      (h : ContDiffAt ℝ ∞ f z) (v : ℂ) :
      ContDiffAt ℝ 2 (fun q : ℝ × ℂ => planePartial v f q.2) (0,z) :=
    (((h.fderiv_right (m := 2) (by simp)).clm_apply contDiffAt_const).comp (0,z) contDiffAt_snd)
  have tang (v : ℂ) : ContDiffAt ℝ 2 (T v) (0,z) :=
    (psm dy v).add (contDiffAt_fst.smul (((psm du v).smul
      ((dn.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)).comp (0,z) contDiffAt_snd)).add
      (((du.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)).comp (0,z) contDiffAt_snd).smul (psm dn v))))
  have dot (v w : ℂ) : ContDiffAt ℝ 2 (fun q => T v q ⬝ᵥ T w q) (0,z) :=
    ContDiffAt.sum fun j _ => ((contDiffAt_pi.mp (tang v)) j).mul ((contDiffAt_pi.mp (tang w)) j)
  have nz : (T 1 (0,z) ⬝ᵥ T 1 (0,z))*(T I (0,z) ⬝ᵥ T I (0,z))-(T 1 (0,z) ⬝ᵥ T I (0,z))^2 ≠ 0 := by
    simpa [T] using positive.ne'
  have gram := (Real.contDiffAt_sqrt nz).comp (0,z) (((dot 1 1).mul (dot I I)).sub ((dot 1 I).pow 2))
  apply gram.congr_of_eventuallyEq
  have nearby {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℂ → E} (h : ContDiffAt ℝ ∞ f z) :
      ∀ᶠ q : ℝ × ℂ in 𝓝 (0,z), DifferentiableAt ℝ f q.2 :=
    (continuous_snd.continuousAt.eventually ((h.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num))).mono
      fun _ hw => hw.differentiableAt one_ne_zero
  filter_upwards [nearby dy,nearby du,nearby dn] with q ydiff udiff ndiff
  exact congrFun (coordinateAreaDensity_normal_displacement ydiff udiff ndiff) q.1

/-- A test supported in the physical region leaves the actual area
density identically constant on its exterior, in every chart. -/
theorem physical_normal_area_unchanged_off_support {M : Type*} [TopologicalSpace M]
    (X N : M → Fin 3 → ℝ) (u : M → ℝ) (e : OpenPartialHomeomorph M ℂ) {z : ℂ}
    (hz : z∈e.target) (off : e.symm z ∉ tsupport u) (s : ℝ) :
    coordinateAreaDensity ((fun p => X p+s • (u p • N p)) ∘ e.symm) z=coordinateAreaDensity (X ∘ e.symm) z := by
  apply coordinateAreaDensity_congr_local
  filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp off).comp_tendsto (e.symm.continuousAt hz).tendsto] with w hw
  change X (e.symm w)+s • (u (e.symm w) • N (e.symm w))=X (e.symm w)
  simp [show u (e.symm w)=0 from hw]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_chart_normal_area_hessian
#print axioms TwoAxisHelicoid.coordinate_normal_variation_density_smooth
#print axioms TwoAxisHelicoid.partitioned_physical_pointwise_area_hessian
#print axioms TwoAxisHelicoid.physical_normal_area_unchanged_off_support
