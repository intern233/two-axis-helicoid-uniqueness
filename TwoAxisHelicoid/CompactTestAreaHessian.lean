import TwoAxisHelicoid.CompactTestRelativeArea
import TwoAxisHelicoid.CompactSliceIntegralHessian

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Matrix Topology InnerProductSpace
open scoped ContDiff Manifold Topology

universe u

theorem compact_test_relative_area_hessian {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (X N : M → Fin 3 → ℝ)
    (hX : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (normal : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target,
      N (e.symm z)=harmonicChartNormal (X ∘ e.symm) z) (v : M → ℝ)
    (smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ v) (P : CompactTestChartCover (tsupport v)) :
    HasDerivAt (deriv (P.relativeArea X N v)) (P.jacobiForm X v) 0 := by
  classical
  let area (i : P.indices) (s : ℝ) (z : ℂ) :=
    coordinateAreaDensity ((fun p => X p+s • (v p • N p)) ∘ (P.chart i).symm) z
  let base (i : P.indices) (z : ℂ) := coordinateAreaDensity (X ∘ (P.chart i).symm) z
  let energy (i : P.indices) (z : ℂ) :=
    planePartial 1 (v ∘ (P.chart i).symm) z^2+planePartial I (v ∘ (P.chart i).symm) z^2-
      jacobiPotentialDensity (X ∘ (P.chart i).symm) z*(v ((P.chart i).symm z))^2
  let w (i : P.indices) := P.weight i ∘ (P.chart i).symm
  let K (i : P.indices) := P.chart i '' tsupport (P.weight i)
  let F (i : P.indices) (q : ℝ × ℂ) := w i q.2*(area i q.1 q.2-base i q.2)
  let J (i : P.indices) (s : ℝ) := ∫ z in K i, F i (s,z)
  have ck (i : P.indices) : IsCompact (K i) := (P.compact i).image_of_continuousOn
    ((P.chart i).continuousOn.mono (P.supported i))
  have sub (i : P.indices) : K i ⊆ (P.chart i).target := by
    rintro _ ⟨p,hp,rfl⟩
    exact (P.chart i).map_source (P.supported i hp)
  have cut (i : P.indices) (f : ℂ → ℝ) :
      (∫ z in (P.chart i).target, w i z*f z)=∫ z in K i, w i z*f z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (P.chart i).open_target.measurableSet (sub i)
    intro z hz
    have away : (P.chart i).symm z ∉ tsupport (P.weight i) := fun mem => hz.2 ⟨_,mem,(P.chart i).right_inv hz.1⟩
    exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport away) _
  have reg (i : P.indices) (z : ℂ) (hz : z ∈ K i) : ContDiffAt ℝ 2 (F i) (0,z) := by
    let e := P.chart i
    have ez := sub i hz
    have data := harmonic_physical_chart_normal_smooth hX normal (P.member i) ez
    have gram : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => area i q.1 q.2) (0,z) :=
      coordinate_normal_variation_density_smooth data.1 data.2.1 (smooth_scalar_in_maximal_complex_chart smooth (P.member i) ez) data.2.2
    have cz : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => ((0:ℝ),q.2)) (0,z) := contDiffAt_const.prodMk contDiffAt_snd
    have zero : (fun q : ℝ × ℂ => area i 0 q.2) = fun q => base i q.2 := by
      funext q
      simp [area,base]
    have baseline : ContDiffAt ℝ 2 (fun q : ℝ × ℂ => base i q.2) (0,z) := by
      rw [← zero]
      exact gram.comp (f := fun q : ℝ × ℂ => ((0:ℝ),q.2))
        (g := fun q : ℝ × ℂ => area i q.1 q.2) (0,z) cz
    exact (((smooth_scalar_in_maximal_complex_chart (P.smooth i) (P.member i) ez).of_le
      (show (2:ℕ∞ω) ≤ ∞ by simp)).comp (0,z) contDiffAt_snd).mul (gram.sub baseline)
  have point (i : P.indices) (z : ℂ) (hz : z ∈ K i) :
      deriv (deriv (fun s => F i (s,z))) 0 = w i z*energy i z := by
    let e := P.chart i
    have ez := sub i hz
    let Y := X ∘ e.symm
    have germ : ∀ᶠ p in 𝓝 z, (∀ j, HarmonicAt (fun x => Y x j) p) ∧
        ConformalCoordinateDerivatives Y p ∧ Function.Injective (fderiv ℝ Y p) := by
      filter_upwards [e.open_target.mem_nhds ez] with p hp
      exact harmonic_immersion_chart_maximal hX (P.member i) p hp
    have hu := (smooth_scalar_in_maximal_complex_chart smooth (P.member i) ez).differentiableAt (by simp)
    have val := (harmonic_chart_normal_area_hessian germ hu).deriv
    have same : (fun s => area i s z)=fun s => coordinateAreaDensity
        (fun p => (X ∘ e.symm) p+s • ((v ∘ e.symm) p • harmonicChartNormal (X ∘ e.symm) p)) z := by
      funext s
      apply coordinateAreaDensity_congr_local
      filter_upwards [e.open_target.mem_nhds ez] with p hp
      exact congrArg (fun n => X (e.symm p)+s • (v (e.symm p) • n)) (normal e (P.member i) p hp)
    simp only [F,deriv_const_mul_field',deriv_const_mul_field,deriv_sub_const_fun]
    rw [same,val]
    rfl
  have patch (i : P.indices) := compact_slice_integral_hessian (ck i) (ck i).measurableSet
    (Subset.rfl : K i ⊆ K i) (reg i)
  have all : ∀ᶠ s in 𝓝 (0:ℝ), ∀ i : P.indices, DifferentiableAt ℝ (J i) s :=
    Filter.eventually_all.mpr (fun i => (patch i).1)
  have first : deriv (fun s : ℝ => ∑ i, J i s) =ᶠ[𝓝 0] fun s => ∑ i, deriv (J i) s :=
    all.mono fun _ hs => deriv_fun_sum fun i _ => hs i
  have value (i : P.indices) : HasDerivAt (deriv (J i))
      (∫ z in (P.chart i).target, w i z*energy i z) 0 := by
    rw [cut]
    convert (patch i).2 using 1
    exact setIntegral_congr_fun (ck i).measurableSet (fun z hz => (point i z hz).symm)
  have sameArea : P.relativeArea X N v = fun s => ∑ i, J i s :=
    funext (fun s => Finset.sum_congr rfl (fun i _ => cut i (fun z => area i s z-base i z)))
  rw [sameArea]
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => value i)).congr_of_eventuallyEq first

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_test_relative_area_hessian
