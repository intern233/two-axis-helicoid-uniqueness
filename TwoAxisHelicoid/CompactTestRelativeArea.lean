import TwoAxisHelicoid.HarmonicChartNormalAreaGeometry
import TwoAxisHelicoid.CompactTestChartCover

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Matrix Topology InnerProductSpace
open scoped ContDiff Manifold Topology

universe u

private theorem area_eq_tangent_gram {Y : ℂ → Fin 3 → ℝ} {z : ℂ} (hy : DifferentiableAt ℝ Y z) :
    coordinateAreaDensity Y z = Real.sqrt ((planePartial 1 Y z ⬝ᵥ planePartial 1 Y z)*
      (planePartial I Y z ⬝ᵥ planePartial I Y z)-(planePartial 1 Y z ⬝ᵥ planePartial I Y z)^2) := by
  have x := (complex_line_planePartial_hasDerivAt hy 1).deriv
  simp only [mul_one] at x
  unfold coordinateAreaDensity
  simp only [mul_comm (I:ℂ),x,(complex_line_planePartial_hasDerivAt hy I).deriv]

private theorem area_eq_cross {Y : ℂ → Fin 3 → ℝ} {z : ℂ} (hy : DifferentiableAt ℝ Y z) :
    coordinateAreaDensity Y z=Real.sqrt (surfaceTangentCross Y z ⬝ᵥ surfaceTangentCross Y z) := by
  rw [area_eq_tangent_gram hy]
  simp only [surfaceTangentCross,cross_dot_cross,planePartial,
    dotProduct_comm (fderiv ℝ Y z I) (fderiv ℝ Y z 1),pow_two]

private theorem chart_area_continuous {Y : ℂ → Fin 3 → ℝ} {T : Set ℂ} (op : IsOpen T)
    (sm : ∀ z∈T, ContDiffAt ℝ 1 Y z) : ContinuousOn (coordinateAreaDensity Y) T := by
  intro z hz
  have tang (v : ℂ) : ContinuousAt (planePartial v Y) z :=
    ((sm z hz).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  have dot (v w : ℂ) : ContinuousAt (fun p => planePartial v Y p ⬝ᵥ planePartial w Y p) z := by
    have term (j : Fin 3) : ContinuousAt (fun p => planePartial v Y p j*planePartial w Y p j) z :=
      ((continuousAt_apply j _).comp (tang v)).mul ((continuousAt_apply j _).comp (tang w))
    simpa only [dotProduct, Fin.sum_univ_three, Pi.add_def] using ((term 0).add (term 1)).add (term 2)
  have body := Real.continuous_sqrt.continuousAt.comp (((dot 1 1).mul (dot I I)).sub ((dot 1 I).pow 2))
  apply (body.congr_of_eventuallyEq ?_).continuousWithinAt
  filter_upwards [op.mem_nhds hz] with p hp
  exact area_eq_tangent_gram ((sm p hp).differentiableAt one_ne_zero)

private theorem chart_area_transform {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (Z : M → Fin 3 → ℝ) (reg : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M,
      ∀ z∈e.target, ContDiffAt ℝ 1 (Z ∘ e.symm) z)
    {e d : OpenPartialHomeomorph M ℂ} (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (hd : d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) {z : ℂ} (hz : z∈(e.symm.trans d).source) :
    coordinateAreaDensity (Z ∘ e.symm) z=
      ‖deriv (e.symm.trans d) z‖^2*coordinateAreaDensity (Z ∘ d.symm) ((e.symm.trans d) z) := by
  let t := e.symm.trans d
  have dt := (complexAtlas_realized_transition he hd hz).analyticAt.differentiableAt
  have dd : DifferentiableAt ℝ (Z ∘ d.symm) (t z) :=
    (reg d hd (t z) (d.map_source hz.2)).differentiableAt one_ne_zero
  have same : Z ∘ e.symm =ᶠ[𝓝 z] (Z ∘ d.symm) ∘ t := by
    filter_upwards [t.open_source.mem_nhds hz] with w hw
    exact congrArg Z (d.left_inv hw.2).symm
  have jac : planeRealJacobian (fderiv ℝ t z) = ‖deriv t z‖^2 := by
    rw [(dt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv,Complex.sq_norm]
    change (1*deriv t z).re*(I*deriv t z).im-(1*deriv t z).im*(I*deriv t z).re=_
    simp only [one_mul,Complex.I_mul_re,Complex.I_mul_im,Complex.normSq_apply]
    ring
  change coordinateAreaDensity (Z ∘ e.symm) z = ‖deriv t z‖^2*coordinateAreaDensity (Z ∘ d.symm) (t z)
  rw [area_eq_cross ((reg e he _ hz.1).differentiableAt one_ne_zero),area_eq_cross dd,
    surfaceTangentCross_coordinate_change same dd (dt.restrictScalars ℝ),jac]
  let k := ‖deriv t z‖^2
  let V := surfaceTangentCross (Z ∘ d.symm) (t z)
  change Real.sqrt ((k • V) ⬝ᵥ (k • V))=k*Real.sqrt (V ⬝ᵥ V)
  simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [show k*(k*(V ⬝ᵥ V))=k^2*(V ⬝ᵥ V) by ring,Real.sqrt_mul (sq_nonneg k),Real.sqrt_sq (sq_nonneg _)]

/-- Finite relative area and the compactly supported energy in a chosen
atlas cover. Both use the same partition and Lebesgue chart integrals. -/
noncomputable def CompactTestChartCover.relativeArea {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    {K : Set M} (P : CompactTestChartCover K) (X N : M → Fin 3 → ℝ) (v : M → ℝ) (s : ℝ) : ℝ :=
  P.integral (fun e z => coordinateAreaDensity ((fun p => X p+s • (v p • N p)) ∘ e.symm) z-
    coordinateAreaDensity (X ∘ e.symm) z)

noncomputable def CompactTestChartCover.jacobiForm {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    {K : Set M} (P : CompactTestChartCover K) (X : M → Fin 3 → ℝ) (v : M → ℝ) : ℝ :=
  P.integral (fun e z => planePartial 1 (v ∘ e.symm) z^2+planePartial I (v ∘ e.symm) z^2-
    jacobiPotentialDensity (X ∘ e.symm) z*(v (e.symm z))^2)

/-- The unrestricted chart-cover integral is literally the intrinsic
Jacobi integrand of the manuscript with its induced area measure. -/
theorem compact_test_jacobi_form_intrinsic {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {K : Set M} (P : CompactTestChartCover K)
    (X : M → Fin 3 → ℝ) (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) (v : M → ℝ) :
    P.jacobiForm X v=P.integral (fun e z =>
      let Y := X ∘ e.symm
      let V := v ∘ e.symm
      let g := planePartial 1 Y z ⬝ᵥ planePartial 1 Y z
      ((planePartial 1 V z^2+planePartial I V z^2)/g-jacobiPotentialDensity Y z/g*(V z)^2)*g) := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_congr_fun (P.chart i).open_target.measurableSet
  intro z hz
  let Y := X ∘ (P.chart i).symm
  have germ : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun x => Y x j) w) ∧
      ConformalCoordinateDerivatives Y w ∧ Function.Injective (fderiv ℝ Y w) := by
    filter_upwards [(P.chart i).open_target.mem_nhds hz] with w hw
    exact harmonic_immersion_chart_maximal hX (P.member i) w hw
  have pos := (harmonic_chart_weingarten_frame germ).metric_pos
  dsimp only [Y] at pos
  dsimp only [Function.comp_apply] at pos ⊢
  field_simp [pos.ne']

theorem harmonic_physical_chart_normal_smooth {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {X N : M → Fin 3 → ℝ}
    (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (normal : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target,
      N (e.symm z)=harmonicChartNormal (X ∘ e.symm) z)
    {e : OpenPartialHomeomorph M ℂ} (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) {z : ℂ} (hz : z ∈ e.target) :
    ContDiffAt ℝ ∞ (X ∘ e.symm) z ∧ ContDiffAt ℝ ∞ (N ∘ e.symm) z ∧
      0 < (planePartial 1 (X ∘ e.symm) z ⬝ᵥ planePartial 1 (X ∘ e.symm) z)*
        (planePartial I (X ∘ e.symm) z ⬝ᵥ planePartial I (X ∘ e.symm) z)-
        (planePartial 1 (X ∘ e.symm) z ⬝ᵥ planePartial I (X ∘ e.symm) z)^2 := by
  obtain ⟨h,c,i⟩ := harmonic_immersion_chart_maximal hX he z hz
  have an : AnalyticAt ℝ (X ∘ e.symm) z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (h j)
  have data := harmonicChartNormal_data an c i
  refine ⟨an.contDiffAt,data.1.contDiffAt.congr_of_eventuallyEq ?_,?_⟩
  · filter_upwards [e.open_target.mem_nhds hz] with w hw
    exact normal e he w hw
  rw [← data.2.2.1,data.2.2.2.1]
  nlinarith [sq_pos_of_pos data.2.1]

theorem compact_test_relative_area_independent {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (X N : M → Fin 3 → ℝ)
    (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (normal : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target,
      N (e.symm z)=harmonicChartNormal (X ∘ e.symm) z) (v : M → ℝ)
    (smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ v) (P Q : CompactTestChartCover (tsupport v)) :
    P.relativeArea X N v = Q.relativeArea X N v := by
  funext s
  let Z := fun p => X p+s • (v p • N p)
  have original e he z hz : ContDiffAt ℝ 1 (X ∘ (e : OpenPartialHomeomorph M ℂ).symm) z :=
    (harmonic_physical_chart_normal_smooth hX normal he hz).1.of_le (by simp)
  have varied (e : OpenPartialHomeomorph M ℂ) (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
      (z : ℂ) (hz : z∈e.target) : ContDiffAt ℝ 1 (Z ∘ e.symm) z := by
    obtain ⟨dy, dn, _⟩ := harmonic_physical_chart_normal_smooth hX normal (e := e) (z := z) he hz
    have dv := smooth_scalar_in_maximal_complex_chart smooth (e := e) (z := z) he hz
    have cs : ContDiffAt ℝ ∞ (fun _ : ℂ => s) z := contDiffAt_const
    exact (dy.add (cs.smul (dv.smul dn))).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  apply compact_test_integral_independent
  · intro e he
    exact (chart_area_continuous e.open_target (varied e he)).sub (chart_area_continuous e.open_target (original e he))
  · intro e _ z hz off
    exact sub_eq_zero.mpr (physical_normal_area_unchanged_off_support X N v e hz off s)
  · intro e he d hd z hz
    rw [chart_area_transform Z varied he hd hz,chart_area_transform X original he hd hz,mul_sub]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_test_relative_area_independent
#print axioms TwoAxisHelicoid.compact_test_jacobi_form_intrinsic
