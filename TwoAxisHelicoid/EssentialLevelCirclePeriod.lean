import TwoAxisHelicoid.MarkedTorusCircleCoordinates
import TwoAxisHelicoid.PlaneCircleWinding
import TwoAxisHelicoid.SmoothTorusCurveLift

namespace TwoAxisHelicoid
open Set Complex Topology
open scoped ContDiff Manifold

/-- A real angle on one closed traversal with matching endpoints descends
along any topological parametrization of a circle. -/
theorem real_angle_from_closed_traversal {C : Type*} [TopologicalSpace C]
    (e : OrientationCircle ≃ₜ C) (φ : C → Circle) {a : ℝ → ℝ} (ca : Continuous a)
    (ends : a 0=a 1) (phase : ∀ t : ℝ, normalizedPhase (a t)=φ (e (t : OrientationCircle))) :
    ∃ f : ContinuousMap C ℝ, ∀ q, normalizedPhase (f q)=φ q := by
  let u : ContinuousMap OrientationCircle ℝ :=
    ⟨AddCircle.liftIco 1 0 a,AddCircle.liftIco_zero_continuous ends ca.continuousOn⟩
  refine ⟨u.comp e.symm,fun q => ?_⟩
  let t := AddCircle.equivIco (1:ℝ) 0 (e.symm q)
  have ht : ((t.1:ℝ):OrientationCircle)=e.symm q := AddCircle.coe_equivIco
  change normalizedPhase (a t.1)=φ q
  rw [phase,ht,e.apply_symm_apply]

/-- Any actual plane traversal over a circle parametrization has a fixed
lattice displacement. If it were zero, the two real coordinates of
the traversal would descend to continuous angles on the whole component. -/
theorem nonlifting_traversal_displacement {C : Type*} [TopologicalSpace C]
    (L : PeriodPair) (e : OrientationCircle ≃ₜ C) (q : C → PeriodTorus L)
    (H : PeriodTorus L ≃ₜ Circle × Circle)
    (marked : ∀ z, H (periodTorusProjection L z)=planeCircleCoordinates L z)
    (obstruct : ¬∃ a b : ContinuousMap C ℝ, ∀ x, normalizedPhase (a x)=(H (q x)).1 ∧
      normalizedPhase (b x)=(H (q x)).2)
    (ξ : ℝ → ℂ) (cont : Continuous ξ)
    (proj : ∀ t : ℝ, periodTorusProjection L (ξ t)=q (e (t:OrientationCircle))) :
    ∃ period : ℂ, period≠0 ∧ period∈L.lattice ∧ ∀ t, ξ (t+1)=ξ t+period := by
  let g := fun t : ℝ => q (e (t:OrientationCircle))
  have per : Function.Periodic g 1 := by
    intro t
    exact congrArg (fun θ => q (e θ)) (AddCircle.coe_add_period (1:ℝ) t)
  let period := ξ 1-ξ 0
  have lat : period∈L.lattice := (periodTorusProjection_eq_iff L _ _).mp
    ((proj 0).trans ((show g 0=g 1 by simpa using (per 0).symm).trans (proj 1).symm))
  let a := fun t => L.basis.repr (ξ t) 0
  let b := fun t => L.basis.repr (ξ t) 1
  have ca : Continuous a := (L.basis.coord 0).continuous_of_finiteDimensional.comp cont
  have cb : Continuous b := (L.basis.coord 1).continuous_of_finiteDimensional.comp cont
  have coords (t : ℝ) : (normalizedPhase (a t),normalizedPhase (b t))=H (q (e (t:OrientationCircle))) := by
    rw [← proj,marked]
    rfl
  have nonzero : period≠0 := by
    intro zero
    have same : ξ 0=ξ 1 := (sub_eq_zero.mp zero).symm
    obtain ⟨A,ra⟩ := real_angle_from_closed_traversal e (fun c => (H (q c)).1) ca
      (congrArg (fun z => L.basis.repr z 0) same) (fun t => congrArg Prod.fst (coords t))
    obtain ⟨B,rb⟩ := real_angle_from_closed_traversal e (fun c => (H (q c)).2) cb
      (congrArg (fun z => L.basis.repr z 1) same) (fun t => congrArg Prod.snd (coords t))
    exact obstruct ⟨A,B,fun x => ⟨ra x,rb x⟩⟩
  refine ⟨period,nonzero,lat,?_⟩
  apply congrFun
  apply (periodTorusProjection_isCoveringMap L).eq_of_comp_eq
    (cont.comp (continuous_id.add continuous_const)) (cont.add continuous_const) _ (0:ℝ)
  · change ξ (0+1)=ξ 0+period
    dsimp [period]; abel
  · funext t
    change periodTorusProjection L (ξ (t+1))=periodTorusProjection L (ξ t+period)
    rw [periodTorusProjection_add_lattice L _ _ lat,proj,proj]
    exact per t

/-- A component homeomorphic to a circle on which the two marked phase
coordinates do not simultaneously lift has nonzero lattice displacement.
The plane curve and all its translates are obtained from the actual
smooth quotient parametrization. -/
theorem nonlifting_level_circle_has_nonzero_period {C : Type*} [TopologicalSpace C]
    (L : PeriodPair) (e : OrientationCircle ≃ₜ C) (q : C → PeriodTorus L)
    (H : PeriodTorus L ≃ₜ Circle × Circle)
    (marked : ∀ z, H (periodTorusProjection L z)=planeCircleCoordinates L z)
    (obstruct : ¬∃ a b : ContinuousMap C ℝ, ∀ x, normalizedPhase (a x)=(H (q x)).1 ∧
      normalizedPhase (b x)=(H (q x)).2)
    (g : ℝ → PeriodTorus L) (smooth : ContMDiff 𝓘(ℝ) 𝓘(ℝ,ℂ) 1 g)
    (runs : ∀ t : ℝ, g t=q (e (t:OrientationCircle))) :
    ∃ (ξ : ℝ → ℂ) (period : ℂ), ContDiff ℝ 1 ξ ∧ (∀ t, periodTorusProjection L (ξ t)=g t) ∧
      period≠0 ∧ period∈L.lattice ∧ ∀ t, ξ (t+1)=ξ t+period := by
  obtain ⟨z,hz⟩ : ∃ z : ℂ, periodTorusProjection L z=g 0 :=
    Quotient.exists_rep (g 0)
  obtain ⟨ξ,sm,_,proj⟩ := smooth_torus_curve_has_plane_lift L g smooth z hz
  obtain ⟨period,nz,lat,shift⟩ := nonlifting_traversal_displacement L e q H marked obstruct ξ sm.continuous
    (fun t => (proj t).trans (runs t))
  exact ⟨ξ,period,sm,proj,nz,lat,shift⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.nonlifting_traversal_displacement
#print axioms TwoAxisHelicoid.nonlifting_level_circle_has_nonzero_period
