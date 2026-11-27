import TwoAxisHelicoid.SmoothCompactFieldOrbit
import TwoAxisHelicoid.SmoothTranslatedPlaneFlux
import TwoAxisHelicoid.SmoothVariationalDependence
import TwoAxisHelicoid.FiniteEnergyAffineRegularity

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter InnerProductSpace
open scoped ContDiff RealInnerProductSpace

/-- The unique whole-plane affine correction for smooth elliptic coefficients
has an infinitely differentiable translation orbit in the actual L² norm. -/
theorem smooth_orbit_of_actual_plane_corrector {A B C : ℂ → ℝ}
    (sa : ContDiff ℝ ∞ A) (sb : ContDiff ℝ ∞ B) (sc : ContDiff ℝ ∞ C)
    {K : Set ℂ} (hk : IsCompact K) (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1)
    (T : Lp ℂ 2 (volume:Measure ℂ) →L[ℝ] Lp ℂ 2 (volume:Measure ℂ))
    (acts : ∀ w, ⇑(T w) =ᵐ[volume] (fun z => planeMetricFlux A B C z (w z))) {c : ℝ}
    (hc : 0<c) (low : ∀ w, c*‖w‖^2≤⟪T w,w⟫_ℝ)
    (b u : Lp ℂ 2 (volume:Measure ℂ)) (rep : ⇑b =ᵐ[volume] planeAffineFluxLoad A B C)
    (hu : u∈planeDirichletGradients volume univ)
    (orth : ∀ w∈planeDirichletGradients volume univ, ⟪T u-b,w⟫_ℝ=0) :
    ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t u) := by
  let E := Lp ℂ 2 (volume:Measure ℂ)
  let S := planeDirichletGradients volume univ
  have cl : IsClosed (S : Set E) := Submodule.isClosed_topologicalClosure _
  obtain ⟨P,sP,point⟩ := exists_smooth_translated_plane_flux sa sb sc hk off
  have sb' := smooth_compact_field_translation (planeAffineFluxLoad_smooth sa sb sc)
    (planeAffineFluxLoad_compact hk off) b rep
  have cov (t : ℂ) (v : E) : P t (planeFieldTranslate t v)=planeFieldTranslate t (T v) := by
    apply Lp.ext
    have sh := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp (acts v)
    filter_upwards [point t (planeFieldTranslate t v),planeFieldTranslate_ae t v,planeFieldTranslate_ae t (T v),sh]
      with z h1 h2 h3 h4
    change T v (z+t)=planeMetricFlux A B C (z+t) (v (z+t)) at h4
    rw [h1,h2,h3,h4]
  have ell (t : ℂ) : ∃ k : ℝ, 0<k ∧ ∀ v, k*‖v‖^2≤⟪P t v,v⟫_ℝ := by
    refine ⟨c,hc,?_⟩
    intro v
    let w := planeFieldTranslate (-t) v
    have inv : planeFieldTranslate t w=v := planeFieldTranslate_cancel t v
    calc
      c*‖v‖^2 = c*‖w‖^2 := by rw [←inv,(planeFieldTranslate t).norm_map]
      _ ≤ ⟪T w,w⟫_ℝ := low w
      _ = ⟪P t v,v⟫_ℝ := by rw [←inv,cov,(planeFieldTranslate t).inner_map_map]
  let v := fun t : ℂ => (⟨planeFieldTranslate t u,planeFieldTranslate_mem_gradients t hu⟩ : S)
  have sol (t : ℂ) (w : S) : ⟪P t (v t).val-planeFieldTranslate t b,w.val⟫_ℝ=0 := by
    change ⟪P t (planeFieldTranslate t u)-planeFieldTranslate t b,w.val⟫_ℝ=0
    rw [cov,←map_sub]
    exact planeFieldTranslate_preserves_zero_flux t _ orth w w.2
  exact S.subtypeL.contDiff.comp (smooth_coercive_variational_solution S cl P _ sP sb' ell v sol)

/-- The smooth energy-space orbit and the original coefficient equation hold
for one and the same uniquely specified finite-energy variational solution. -/
theorem exists_actual_plane_corrector_smooth_orbit {A B C : ℂ → ℝ}
    (sa : ContDiff ℝ ∞ A) (sb : ContDiff ℝ ∞ B) (sc : ContDiff ℝ ∞ C) (ha : ∀ z, 0<A z)
    (det : ∀ z, A z*C z-(B z)^2=1) {K : Set ℂ} (hk : IsCompact K)
    (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1) :
    ∃ (T : Lp ℂ 2 (volume:Measure ℂ) →L[ℝ] Lp ℂ 2 (volume:Measure ℂ))
      (b u : Lp ℂ 2 (volume:Measure ℂ)), u∈planeDirichletGradients volume univ ∧
      (∀ w, ⇑(T w) =ᵐ[volume] (fun z => planeMetricFlux A B C z (w z))) ∧
      (⇑b =ᵐ[volume] planeAffineFluxLoad A B C) ∧
      (∀ w∈planeDirichletGradients volume univ, ⟪T u-b,w⟫_ℝ=0) ∧
      ContDiff ℝ ∞ (fun t : ℂ => planeFieldTranslate t u) := by
  obtain ⟨k,T,b,k1,acts,low,rep,u,sol,_⟩ :=
    exists_whole_plane_affine_corrector sa.continuous sb.continuous sc.continuous ha det hk off
  have eq (w : Lp ℂ 2 (volume:Measure ℂ)) (hw : w∈planeDirichletGradients volume univ) :
    ⟪T u.val-b,w⟫_ℝ=0 := sol ⟨w,hw⟩
  refine ⟨T,b,u.val,u.2,acts,rep,eq,?_⟩
  exact smooth_orbit_of_actual_plane_corrector sa sb sc hk off T acts (inv_pos.mpr (by linarith)) low b u.val rep u.2 eq
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_orbit_of_actual_plane_corrector
#print axioms TwoAxisHelicoid.exists_actual_plane_corrector_smooth_orbit
