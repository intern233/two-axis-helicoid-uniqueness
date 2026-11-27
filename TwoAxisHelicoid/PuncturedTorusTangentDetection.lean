import TwoAxisHelicoid.PuncturedGeneratorSpinLift
import TwoAxisHelicoid.PuncturedMarkedTangentFrame
import TwoAxisHelicoid.RegularTorusFrameCurves

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff Manifold

variable (L : PeriodPair) {F : PeriodTorus L → Fin 3 → ℝ}
variable (hsm : ∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
variable (hi : ∀ q ≠ 0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))

include hsm hi in
private theorem punctured_lift_derivative_continuous :
    Continuous (fun z : PuncturedLatticePlane L => fderiv ℝ (F ∘ periodTorusProjection L) z.1) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact ((spatial_torus_lift_regular_at L F z.2 hsm hi).1.continuousAt_fderiv (by simp)).comp
    (f := (Subtype.val : PuncturedLatticePlane L → ℂ)) continuous_subtype_val.continuousAt

/-- A simultaneous closed lift of the two real tangent-adapted generator
frames gives a global quaternion lift of the reference differential frame
on the punctured surface, even when the marking is nonsmooth at the cap. -/
theorem punctured_ambient_lift_of_generators (hgen : ∀ i, CapGeneratorAmbientSpinCloses L F i) :
    ∃ q : C(PuncturedPeriodTorus L,UnitQuaternion), ∀ z,
      unitQuaternionFrame (q z) = puncturedMarkedTangentFrame L F hsm hi z := by
  apply (punctured_frame_global_lift_iff L _).mpr
  intro i
  let γ := puncturedBasisLine L i
  let D := fderiv ℝ (F ∘ periodTorusProjection L)
  let A : C(unitInterval,ℂ →L[ℝ] (Fin 3 → ℝ)) := ⟨fun t => D (γ t.1).1,
    (punctured_lift_derivative_continuous L hsm hi).comp ((puncturedBasisLine_continuous L i).comp continuous_subtype_val)⟩
  have hiA (t : unitInterval) : Function.Injective (A t) := (spatial_torus_lift_regular_at L F (γ t.1).2 hsm hi).2
  have hA1 : A 1 = A 0 := by
    change D (periodBasisLine L i 1) = D (periodBasisLine L i 0)
    rw [show periodBasisLine L i 1 = periodBasisLine L i 0+L.basis i by simpa only [zero_add] using periodBasisLine_add_one L i 0]
    exact lifted_fderiv_periodic L F _ _ ((periodGeneratorPeriod_val L i) ▸ (periodGeneratorPeriod L i).2)
  obtain ⟨a,ha,haf⟩ := hgen i
  have hmark : SpatialFrameCurveCloses (fun t => spatialDifferentialFrame (hiA t) (L.basis.ne_zero i)) :=
    ⟨a,ha,fun t => Subtype.ext (haf t)⟩
  obtain ⟨b,hb,hbf⟩ := regular_frame_closed_change_constant A hiA hA1 (L.basis.ne_zero i) one_ne_zero hmark
  exact ⟨b,hb,fun t => (hbf t).trans (puncturedMarkedTangentFrame_projection L F hsm hi (γ t.1)).symm⟩

/-- A regular essential simple curve disjoint from the capped point has a
closed tangent-adapted ambient spin lift whenever both marked lifts close. -/
theorem punctured_ambient_lift_on_essential_curve (hgen : ∀ i, CapGeneratorAmbientSpinCloses L F i)
    {ξ : ℝ → ℂ} (hξ : ContDiff ℝ 1 ξ) (hx : ∀ t, ξ t ∉ L.lattice)
    {period : ℂ} (hω : period ≠ 0) (hωL : period ∈ L.lattice) (hp : ∀ t, ξ (t+1) = ξ t+period)
    (hr : ∀ t, deriv ξ t ≠ 0) (hinj : ∀ t h : ℝ, h ∈ Ioo (0:ℝ) 1 → ξ (t+h) ≠ ξ t) :
    SpatialFrameCurveCloses (fun t => spatialDifferentialFrame (spatial_torus_lift_regular_at L F (hx t.1) hsm hi).2 (hr t.1)) := by
  let γ : C(unitInterval,PuncturedLatticePlane L) := ⟨fun t => ⟨ξ t.1,hx t.1⟩,
    (hξ.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let D := fderiv ℝ (F ∘ periodTorusProjection L)
  let A : C(unitInterval,ℂ →L[ℝ] (Fin 3 → ℝ)) := ⟨fun t => D (γ t).1,
    (punctured_lift_derivative_continuous L hsm hi).comp γ.continuous⟩
  have hiA (t : unitInterval) : Function.Injective (A t) := (spatial_torus_lift_regular_at L F (hx t.1) hsm hi).2
  have h1 : ξ 1 = ξ 0+period := by simpa only [zero_add] using hp 0
  have hA : A 1 = A 0 := by change D (ξ 1) = D (ξ 0); rw [h1]; exact lifted_fderiv_periodic L F _ _ hωL
  apply essential_frame_closed_of_fixed_direction hξ hω hp hr hinj A hiA hA
  obtain ⟨q,hq⟩ := punctured_ambient_lift_of_generators L hsm hi hgen
  let v : C(unitInterval,PuncturedPeriodTorus L) := ⟨fun t => puncturedPlaneProjection L (γ t),
    (puncturedPlaneProjection_continuous L).comp γ.continuous⟩
  have he : v 1 = v 0 := by
    apply Subtype.ext
    change periodTorusProjection L (ξ 1) = periodTorusProjection L (ξ 0)
    rw [h1,periodTorusProjection_add_lattice L _ _ hωL]
  exact ⟨q.comp v,congrArg q he,fun t => (hq _).trans (puncturedMarkedTangentFrame_projection L F hsm hi (γ t))⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_ambient_lift_on_essential_curve
