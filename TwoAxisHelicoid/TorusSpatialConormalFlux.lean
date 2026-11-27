import TwoAxisHelicoid.SpatialConormalFlux
import TwoAxisHelicoid.IntrinsicHorizontalTorusFlux

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- Integral of the oriented spatial unit conormal against arclength on
an actual piecewise C¹ path of the punctured torus. Different lifts are
allowed at corners. -/
inductive TorusSpatialConormalIntegral (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) (j : Fin 3) :
    {q r : PuncturedPeriodTorus L} → Path q r → ℝ → Prop
  | refl (q : PuncturedPeriodTorus L) : TorusSpatialConormalIntegral L X j (Path.refl q) 0
  | arc {q r : PuncturedPeriodTorus L} (γ : Path q r) (a : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ)
      (h : ∀ s, (γ s).1 = periodTorusProjection L (a.curve (a.time s))) :
      TorusSpatialConormalIntegral L X j γ (a.spatialConormalFlux (puncturedTorusPullback L X) j)
  | trans {q r s : PuncturedPeriodTorus L} {γ : Path q r} {δ : Path r s} {u v : ℝ} :
      TorusSpatialConormalIntegral L X j γ u → TorusSpatialConormalIntegral L X j δ v →
        TorusSpatialConormalIntegral L X j (γ.trans δ) (u+v)

/-- Exact identification for each genuine lifted arc and concatenation,
with no global choice of lift or curve representative. -/
theorem torus_spatial_conormal_integral_iff (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    {q r : PuncturedPeriodTorus L} (γ : Path q r) (j : Fin 3) (v : ℝ) :
    TorusSpatialConormalIntegral L X j γ v ↔
      ∃ w : ℂ, TorusPathIntegral L (fun z => torusImmersionForms L X z j) γ w ∧ w.im = v := by
  let p := torusImmersionForms L X
  obtain ⟨ha,hn,hD⟩ := torusImmersionForms_regular L X (fun z hz => (hX z hz).1) (fun z hz => (hX z hz).2)
  have ha' (a : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ) :
      a.spatialConormalFlux (puncturedTorusPullback L X) j = (a.integral (fun z => p z j)).im :=
    a.spatialConormalFlux_eq_im _ p hD hn j (fun z hz => (ha z hz j).continuousAt.continuousWithinAt)
  constructor
  · intro h
    induction h with
    | refl q => exact ⟨0,.refl q,rfl⟩
    | arc γ a h => exact ⟨_,.arc γ a h,(ha' a).symm⟩
    | trans _ _ h₁ h₂ =>
      obtain ⟨w,h,hw⟩ := h₁
      obtain ⟨u,h',hu⟩ := h₂
      exact ⟨_,h.trans h',by rw [Complex.add_im,hw,hu]⟩
  · rintro ⟨w,h,rfl⟩
    induction h with
    | refl q => exact .refl q
    | arc γ a h => rw [← ha' a]; exact .arc γ a h
    | trans _ _ h₁ h₂ => exact h₁.trans h₂

def HasSpatialNonverticalFlux (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ) : Prop :=
  ∃ (q : PuncturedPeriodTorus L) (γ : Path q q) (j : Fin 3) (v : ℝ), j ≠ 2 ∧
    TorusSpatialConormalIntegral L X j γ v ∧ v ≠ 0

theorem torus_spatial_nonvertical_flux_iff (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z) :
    HasSpatialNonverticalFlux L X ↔ HasIntrinsicNonverticalFlux L X := by
  constructor
  · rintro ⟨q,γ,j,v,hj,h,hn⟩
    obtain ⟨w,hw,rfl⟩ := (torus_spatial_conormal_integral_iff L X hX γ j v).mp h
    exact ⟨q,γ,j,w,hj,hw,hn⟩
  · rintro ⟨q,γ,j,w,hj,h,hn⟩
    exact ⟨q,γ,j,w.im,hj,(torus_spatial_conormal_integral_iff L X hX γ j w.im).mpr ⟨w,h,rfl⟩,hn⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torus_spatial_nonvertical_flux_iff
