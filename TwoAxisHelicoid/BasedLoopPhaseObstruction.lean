import TwoAxisHelicoid.MarkedTorusCircleCoordinates
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting

namespace TwoAxisHelicoid
open Topology Set
open scoped unitInterval

/-- A pointwise closed lift of every based loop gives a continuous lift
on the whole locally path-connected, path-connected domain. -/
theorem continuous_lift_of_closed_based_lifts {A B E : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace E]
    [PathConnectedSpace A] [LocallyPathConnectedSpace A] {p : E → B}
    (cov : IsCoveringMap p) (f : C(A,B)) (a : A) (e : E) (he : p e=f a)
    (closed : ∀ γ : Path a a, ∃ d : Path e e, ∀ t, p (d t)=f (γ t)) :
    ∃ F : C(A,E), F a=e ∧ p ∘ F=f := by
  apply ExistsUnique.exists (cov.existsUnique_continuousMap_lifts_of_range_le he ?_)
  rintro _ ⟨⟨⟨γ⟩⟩,rfl⟩
  obtain ⟨d,lift⟩ := closed γ
  refine ⟨FundamentalGroup.fromPath (.mk d),?_⟩
  rw [CategoryTheory.End.ext_iff,FundamentalGroup.mapOfEq_apply,FundamentalGroup.map_apply_asHom]
  change ((Path.Homotopic.Quotient.mk d).map ⟨p,cov.continuous⟩).cast he.symm he.symm =
    (Path.Homotopic.Quotient.mk γ).map f
  rw [← Path.Homotopic.Quotient.mk_map,← Path.Homotopic.Quotient.mk_map,← Path.Homotopic.Quotient.mk_cast]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact lift t

/-- Nonexistence of a real angle on a locally path-connected component
is witnessed by one actual based loop with no closed real angle. -/
theorem nonlifting_phase_detected_by_based_loop {A : Type*} [TopologicalSpace A]
    [PathConnectedSpace A] [LocallyPathConnectedSpace A] (φ : C(A,Circle)) (a : A)
    (nonlift : ¬∃ U : C(A,ℝ), ∀ x, normalizedPhase (U x)=φ x) :
    ∃ γ : Path a a, ¬∃ u : C(I,ℝ), u 0=u 1 ∧ ∀ t, normalizedPhase (u t)=φ (γ t) := by
  by_contra! all
  let k := 2*Real.pi
  have hk : k≠0 := by dsimp [k]; positivity
  obtain ⟨e,he⟩ := Circle.exp_surjective (φ a)
  have closed (γ : Path a a) : ∃ d : Path e e, ∀ t, Circle.exp (d t)=φ (γ t) := by
    obtain ⟨u,ends,rep⟩ := all γ
    let d := fun t : I => (k*u t-k*u 0)+e
    have cont : Continuous d := ((continuous_const.mul u.continuous).sub continuous_const).add continuous_const
    have first : d 0=e := by simp [d]
    have last : d 1=e := by simp [d,← ends]
    refine ⟨⟨⟨d,cont⟩,first,last⟩,?_⟩
    intro t
    change Circle.exp ((k*u t-k*u 0)+e)=φ (γ t)
    rw [Circle.exp_add,Circle.exp_sub,he]
    change normalizedPhase (u t)/normalizedPhase (u 0)*φ a=φ (γ t)
    rw [rep,rep,γ.source,div_mul_cancel]
  obtain ⟨F,_,hF⟩ := continuous_lift_of_closed_based_lifts Circle.isCoveringMap_exp φ a e he closed
  apply nonlift
  refine ⟨⟨fun x => F x/k,F.continuous.div_const k⟩,?_⟩
  intro x
  change Circle.exp (k*(F x/k))=φ x
  rw [show k*(F x/k)=F x by field_simp]
  exact congrFun hF x

/-- The two marked phases need only one common test loop. -/
theorem nonlifting_phase_pair_detected_by_loop {A : Type*} [TopologicalSpace A]
    [PathConnectedSpace A] [LocallyPathConnectedSpace A] (H : C(A,Circle×Circle)) (a : A)
    (nonlift : ¬∃ u w : C(A,ℝ), ∀ x, normalizedPhase (u x)=(H x).1 ∧ normalizedPhase (w x)=(H x).2) :
    ∃ γ : Path a a, ¬∃ u w : C(I,ℝ), u 0=u 1 ∧ w 0=w 1 ∧ ∀ t,
      normalizedPhase (u t)=(H (γ t)).1 ∧ normalizedPhase (w t)=(H (γ t)).2 := by
  by_cases fst : ∃ u : C(A,ℝ), ∀ x, normalizedPhase (u x)=(H x).1
  · obtain ⟨u,hu⟩ := fst
    have snd : ¬∃ w : C(A,ℝ), ∀ x, normalizedPhase (w x)=(H x).2 := by
      rintro ⟨w,hw⟩
      exact nonlift ⟨u,w,fun x => ⟨hu x,hw x⟩⟩
    obtain ⟨γ,hγ⟩ := nonlifting_phase_detected_by_based_loop ⟨_,H.continuous.snd⟩ a snd
    refine ⟨γ,?_⟩
    rintro ⟨_,w,_,hw,rep⟩
    exact hγ ⟨w,hw,fun t => (rep t).2⟩
  · obtain ⟨γ,hγ⟩ := nonlifting_phase_detected_by_based_loop ⟨_,H.continuous.fst⟩ a fst
    refine ⟨γ,?_⟩
    rintro ⟨u,_,hu,_,rep⟩
    exact hγ ⟨u,hu,fun t => (rep t).1⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.nonlifting_phase_detected_by_based_loop
#print axioms TwoAxisHelicoid.nonlifting_phase_pair_detected_by_loop
