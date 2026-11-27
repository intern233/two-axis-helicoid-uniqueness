import TwoAxisHelicoid.ParameterizedPlaneFlux
import TwoAxisHelicoid.ParameterizedPlaneLoad
import TwoAxisHelicoid.SmoothFiniteEnergyAffineOrbit

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter InnerProductSpace
open scoped ContDiff RealInnerProductSpace

private theorem constant_background_pairing {A B C : ℂ → ℝ} (q : ℂ)
    (T : Lp ℂ 2 (volume : Measure ℂ) →L[ℝ] Lp ℂ 2 (volume : Measure ℂ))
    (b u : Lp ℂ 2 (volume : Measure ℂ))
    (acts : ∀ w, ⇑(T w) =ᵐ[volume] fun z => planeMetricFlux A B C z (w z))
    (rep : ⇑b =ᵐ[volume] fun z => q-planeMetricFlux A B C z 1)
    {φ : ℂ → ℝ} (s : ContDiff ℝ ∞ φ) (h : HasCompactSupport φ) :
    (∫ z, ⟪planeMetricFlux A B C z (1+u z),planeTestGradient φ z⟫_ℝ) =
      ⟪T u-b,(planeTestGradient_memLp (μ:=volume) s h).toLp (planeTestGradient φ)⟫_ℝ := by
  let m := planeTestGradient_memLp (μ:=volume) s h
  let w := m.toLp (planeTestGradient φ)
  have field : ∀ᵐ z : ℂ, planeMetricFlux A B C z (1+u z)=(T u-b) z+q := by
    filter_upwards [Lp.coeFn_sub (T u) b,acts u,rep] with z hz ht hb
    rw [hz,Pi.sub_apply,ht,hb]
    apply Complex.ext <;> simp [planeMetricFlux] <;> ring
  have eq : (∫ z, ⟪planeMetricFlux A B C z (1+u z),planeTestGradient φ z⟫_ℝ) =
      (∫ z, ⟪(T u-b) z,w z⟫_ℝ + fderiv ℝ φ z q) := by
    apply integral_congr_ae
    filter_upwards [field,m.coeFn_toLp] with z hz hv
    rw [hz,hv,inner_add_left,real_inner_comm (planeTestGradient φ z) q,planeTestGradient_pair]
  have dc := (s.continuous_fderiv (by simp)).clm_apply (continuous_const (y:=q))
  rw [eq,integral_add (L2.integrable_inner (𝕜:=ℝ) (T u-b) w)
    (dc.integrable_of_hasCompactSupport (h.fderiv_apply ℝ q)),←L2.inner_def,
    plane_compact_derivative_integral_zero s h,add_zero]

/-- The actual weak gradients depend jointly smoothly on the scale and the
translation. At the frozen scale the finite-energy correction vanishes. -/
theorem exists_frozen_plane_weak_gradients {A B C : ℂ → ℝ}
    (sa : ContDiff ℝ ∞ A) (sb : ContDiff ℝ ∞ B) (sc : ContDiff ℝ ∞ C) (p : ℂ)
    {k : ℝ} (kp : 0<k) (low : ∀ z x y, (x^2+y^2)/k≤C z*x^2-2*B z*x*y+A z*y^2) :
    ∃ u : ℝ → Lp ℂ 2 (volume:Measure ℂ), u 0=0 ∧ (∀ s, u s∈planeDirichletGradients volume univ) ∧
      ContDiff ℝ ∞ (fun t : ℝ × ℂ => planeFieldTranslate t.2 (u t.1)) ∧
      ∀ s (φ : ℂ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ z, ⟪planeMetricFlux (planeFrozenCoefficient A p s) (planeFrozenCoefficient B p s)
          (planeFrozenCoefficient C p s) z (1+u s z),planeTestGradient φ z⟫_ℝ)=0 := by
  let E := Lp ℂ 2 (volume:Measure ℂ)
  let S := planeDirichletGradients volume univ
  have cl : IsClosed (S : Set E) := Submodule.isClosed_topologicalClosure _
  obtain ⟨T,sT,acts,lower⟩ := exists_frozen_plane_flux_operator sa sb sc p low
  obtain ⟨b,sb',rep⟩ := exists_frozen_plane_load A sb sc p
  have unique (s : ℝ) := coercive_flux_unique_load S cl (T (s,0)) (inv_pos.mpr kp) (lower (s,0)) (b (s,0))
  choose u sol uniq using unique
  have b0 : b (0,0)=0 := by
    apply Lp.ext
    filter_upwards [rep (0,0),Lp.coeFn_zero (E:=ℂ) (p:=2) (μ:=volume)] with z hz hv
    rw [hz,hv]
    apply Complex.ext <;> simp [planeMetricFlux]
  have u0 : u 0=0 := by
    apply (uniq 0 0 ?_).symm
    intro v
    simp [b0]
  have cov (t : ℝ × ℂ) (v : E) : T t (planeFieldTranslate t.2 v)=planeFieldTranslate t.2 (T (t.1,0) v) := by
    apply Lp.ext
    have sh := (measurePreserving_add_right volume t.2).quasiMeasurePreserving.ae_eq_comp (acts (t.1,0) v)
    filter_upwards [acts t (planeFieldTranslate t.2 v),planeFieldTranslate_ae t.2 v,
      planeFieldTranslate_ae t.2 (T (t.1,0) v),sh] with z h1 h2 h3 h4
    rw [h1,h2,h3]
    simpa only [Function.comp_apply,add_zero] using h4.symm
  have bcov (t : ℝ × ℂ) : b t=planeFieldTranslate t.2 (b (t.1,0)) := by
    apply Lp.ext
    have sh := (measurePreserving_add_right volume t.2).quasiMeasurePreserving.ae_eq_comp (rep (t.1,0))
    filter_upwards [rep t,planeFieldTranslate_ae t.2 (b (t.1,0)),sh] with z h1 h2 h3
    rw [h1,h2]
    simpa only [Function.comp_apply,add_zero] using h3.symm
  let v := fun t : ℝ × ℂ => (⟨planeFieldTranslate t.2 (u t.1).val,planeFieldTranslate_mem_gradients t.2 (u t.1).2⟩ : S)
  have sv (t : ℝ × ℂ) (w : S) : ⟪T t (v t).val-b t,w.val⟫_ℝ=0 := by
    change ⟪T t (planeFieldTranslate t.2 (u t.1).val)-b t,w.val⟫_ℝ=0
    rw [cov,bcov,←map_sub]
    exact planeFieldTranslate_preserves_zero_flux t.2 _ (fun y hy => sol t.1 ⟨y,hy⟩) w w.2
  have smooth := smooth_coercive_variational_solution S cl T b sT sb'
    (fun t => ⟨_,inv_pos.mpr kp,lower t⟩) v sv
  refine ⟨fun s => (u s).val,by simp [u0],fun s => (u s).2,S.subtypeL.contDiff.comp smooth,?_⟩
  intro s φ smoothφ h
  have ac (w : E) := acts (s,0) w
  have rc := rep (s,0)
  simp only [add_zero] at ac rc
  rw [constant_background_pairing (planeMetricFlux A B C p 1) (T (s,0)) (b (s,0)) (u s).val ac rc smoothφ h]
  apply sol s
    ⟨_,Submodule.le_topologicalClosure _ (Submodule.subset_span
      ⟨φ,smoothφ,h,subset_univ _,(planeTestGradient_memLp (μ:=volume) smoothφ h).coeFn_toLp⟩)⟩
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_frozen_plane_weak_gradients
