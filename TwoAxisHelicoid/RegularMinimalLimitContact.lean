import TwoAxisHelicoid.MinimalContactSheet
import TwoAxisHelicoid.ContactProjectionMinor

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ContDiff

/-- The full interior first-contact principle in a one-parameter family
of harmonic conformal immersions. No tangent plane, graph direction,
graph ordering or maximum principle is supplied as an assumption. -/
theorem frequent_separation_forces_minimal_sheet_coincidence {F : ℝ × ℂ → Fin 3 → ℝ}
    {t : ℝ} {a b : ℂ} (ab : a ≠ b) (same : F (t,a)=F (t,b))
    (fa : AnalyticAt ℝ F (t,a)) (fb : AnalyticAt ℝ F (t,b))
    (ha : ∀ᶠ z in 𝓝 a, (∀ j, HarmonicAt (fun u => F (t,u) j) z) ∧ ConformalCoordinateDerivatives (fun u => F (t,u)) z)
    (hb : ∀ᶠ z in 𝓝 b, (∀ j, HarmonicAt (fun u => F (t,u) j) z) ∧ ConformalCoordinateDerivatives (fun u => F (t,u)) z)
    (ia : Function.Injective (fderiv ℝ (fun u => F (t,u)) a)) (ib : Function.Injective (fderiv ℝ (fun u => F (t,u)) b))
    {U V : Set ℂ} (hu : U ∈ 𝓝 a) (hv : V ∈ 𝓝 b)
    (sep : ∃ᶠ s in 𝓝 t, ∀ u ∈ U, ∀ v ∈ V, F (s,u) ≠ F (s,v)) :
    ∀ᶠ u in 𝓝 a, F (t,u) ∈ (fun v => F (t,v)) '' V := by
  let X := fun z => F (t,z)
  have tangent := tangent_planes_agree_at_limit_contact F ab same fa.contDiffAt fb.contDiffAt ia ib
    (by simp) hu hv (sep.mono fun s hs u h v hv _ => hs u h v hv)
  obtain ⟨σ,ma,mb⟩ := common_coordinate_minor_of_tangent_eq _ _ ia ib tangent
  let T : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (σ j))
  have injT : Function.Injective T := by
    intro p q eq
    funext j
    obtain ⟨v,rfl⟩ := σ.surjective j
    exact congrFun eq v
  let G := T ∘ F
  let Y := fun z => G (t,z)
  have reidx {z : ℂ} (hz : (∀ j, HarmonicAt (fun u => X u j) z) ∧ ConformalCoordinateDerivatives X z) :
      (∀ j, HarmonicAt (fun u => Y u j) z) ∧ ConformalCoordinateDerivatives Y z :=
    ⟨fun j => hz.1 (σ j),conformal_reindex_coordinates σ hz.2⟩
  have transformed {z : ℂ} (hz : AnalyticAt ℝ F (t,z)) :
      fderiv ℝ Y z=T.comp (fderiv ℝ X z) :=
    (T.hasFDerivAt.comp z (hz.comp (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt).fderiv
  have ga : AnalyticAt ℝ G (t,a) := (T.analyticAt _).comp fa
  have gb : AnalyticAt ℝ G (t,b) := (T.analyticAt _).comp fb
  have det {z : ℂ} (fz : AnalyticAt ℝ F (t,z))
      (d : fderiv ℝ X z 1 (σ 0)*fderiv ℝ X z I (σ 1)-fderiv ℝ X z 1 (σ 1)*fderiv ℝ X z I (σ 0) ≠ 0) :
      fderiv ℝ Y z 1 0*fderiv ℝ Y z I 1-fderiv ℝ Y z 1 1*fderiv ℝ Y z I 0 ≠ 0 := by
    rw [transformed fz]; exact d
  obtain ⟨A⟩ := exists_analytic_contact_sheet ga (spatialGraphProjection_injective _ _ _ (det fa ma))
  obtain ⟨B⟩ := exists_analytic_contact_sheet gb (spatialGraphProjection_injective _ _ _ (det fb mb))
  have minB : horizontalMinor (planePartial 1 Y b) (planePartial I Y b) ≠ 0 := by
    simpa only [horizontalMinor,planePartial,mul_comm (fderiv ℝ Y b I 0) _] using det fb mb
  have im : Function.Injective (fderiv ℝ Y a) := transformed fa ▸ injT.comp ia
  have h := minimal_contact_sheet_germs_coincide ga gb (congrArg T same) (ha.mono fun _ h => reidx h)
    (hb.mono fun _ h => reidx h) im A B minB hu hv (sep.mono fun s hs x hx y hy eq => hs x hx y hy (injT eq))
  filter_upwards [h] with u point
  obtain ⟨v,hv',eq⟩ := point
  exact ⟨v,hv',injT eq⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.frequent_separation_forces_minimal_sheet_coincidence
