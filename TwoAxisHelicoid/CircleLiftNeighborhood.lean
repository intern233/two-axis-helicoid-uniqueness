import TwoAxisHelicoid.MarkedTorusCircleCoordinates
import Mathlib.Topology.TietzeExtension

namespace TwoAxisHelicoid
open Set Complex Topology

/-- A continuous real angle, in turns, that represents the given phase on a set. -/
def PhaseLiftsOn {X : Type*} [TopologicalSpace X] (φ : X → Circle) (D : Set X) : Prop :=
  ∃ u : C(X,ℝ), ∀ x∈D, normalizedPhase (u x)=φ x

theorem PhaseLiftsOn.mono {X : Type*} [TopologicalSpace X] {φ : X → Circle} {A B : Set X}
    (h : PhaseLiftsOn φ B) (sub : A⊆B) : PhaseLiftsOn φ A := by
  obtain ⟨u,eq⟩ := h
  exact ⟨u,fun x hx => eq x (sub hx)⟩

/-- A real angle on a closed set extends as a real-valued function. Its phase
error is one on the set. A branch of the argument of that error corrects the
extension on an entire open neighborhood. -/
theorem phase_lifts_in_a_neighborhood {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {φ : X → Circle} (cφ : Continuous φ) {D : Set X} (cd : IsClosed D)
    (u : C(D,ℝ)) (lifted : ∀ x : D, normalizedPhase (u x)=φ x) :
    ∃ O : Set X, IsOpen O ∧ D⊆O ∧ PhaseLiftsOn φ O := by
  obtain ⟨g,hg⟩ := ContinuousMap.exists_restrict_eq cd u
  let r := fun x : X => φ x / normalizedPhase (g x)
  have ph : Continuous normalizedPhase := Circle.exp.continuous.comp (continuous_const.mul continuous_id)
  have cr : Continuous r := cφ.div' (ph.comp g.continuous)
  have cval : Continuous (fun x => ((r x : Circle):ℂ)) := continuous_subtype_val.comp cr
  have re := continuous_re.comp cval
  let K := {x : X | (1/2:ℝ)≤((r x:Circle):ℂ).re}
  have ck : IsClosed K := isClosed_le continuous_const re
  let angle := fun q : K => ((r q:Circle):ℂ).arg/(2*Real.pi)
  have cangle : Continuous angle := by
    apply Continuous.div_const
    apply continuous_iff_continuousAt.mpr
    intro q
    have good : ((r q.1:Circle):ℂ)∈Complex.slitPlane :=
      Or.inl ((by norm_num : (0:ℝ)<1/2).trans_le q.2)
    have cv : Continuous (fun y : K => ((r y.1:Circle):ℂ)) := cval.comp continuous_subtype_val
    change ContinuousAt (Complex.arg ∘ (fun y : K => ((r y.1:Circle):ℂ))) q
    exact (Complex.continuousAt_arg good).comp (f:=fun y : K => ((r y.1:Circle):ℂ)) (x:=q) cv.continuousAt
  obtain ⟨a,ha⟩ := ContinuousMap.exists_restrict_eq ck (⟨angle,cangle⟩ : C(K,ℝ))
  let O := {x : X | (1/2:ℝ)<((r x:Circle):ℂ).re}
  refine ⟨O,isOpen_lt continuous_const re,?_,g+a,?_⟩
  · intro x hx
    have val : g x=u ⟨x,hx⟩ := DFunLike.congr_fun hg ⟨x,hx⟩
    have unit : r x=1 := by simp [r,val,lifted]
    change (1/2:ℝ)<((r x:Circle):ℂ).re
    rw [unit]
    norm_num
  · intro x hx
    have xpos : (1/2:ℝ)<((r x:Circle):ℂ).re := hx
    have val : a x=((r x:Circle):ℂ).arg/(2*Real.pi) :=
      DFunLike.congr_fun ha (⟨x,xpos.le⟩ : K)
    have cancel (b : ℝ) : 2*Real.pi*(b/(2*Real.pi))=b := by field_simp
    change Circle.exp (2*Real.pi*(g x+a x))=φ x
    rw [mul_add,Circle.exp_add,val,cancel,Circle.exp_arg]
    change normalizedPhase (g x)*(φ x/normalizedPhase (g x))=φ x
    simp

/-- A compact Hausdorff component in an open neighborhood is contained in
a clopen neighborhood of its point lying inside that open set. -/
theorem clopen_inside_component_neighborhood {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] (x : X) {O : Set X} (op : IsOpen O) (sub : connectedComponent x⊆O) :
    ∃ V : Set X, IsClopen V ∧ x∈V ∧ V⊆O := by
  classical
  rw [connectedComponent_eq_iInter_isClopen] at sub
  obtain ⟨t,ht⟩ := op.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun s : {s : Set X // IsClopen s ∧ x∈s} => s.1) (fun s => s.2.1.isClosed)
    (disjoint_compl_left_iff_subset.mpr sub)
  exact ⟨⋂ s∈t,Subtype.val s,isClopen_biInter_finset (fun s _ => s.2.1),mem_iInter₂.mpr (fun s _ => s.2.2),
    disjoint_compl_left_iff_subset.mp ht⟩

theorem PhaseLiftsOn.disjoint_union {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {φ : X → Circle} {A B : Set X} (a : PhaseLiftsOn φ A) (b : PhaseLiftsOn φ B)
    (ca : IsClosed A) (cb : IsClosed B) (dis : Disjoint A B) : PhaseLiftsOn φ (A∪B) := by
  obtain ⟨u,hu⟩ := a
  obtain ⟨v,hv⟩ := b
  obtain ⟨t,ta,tb,_⟩ := exists_continuous_zero_one_of_isClosed ca cb dis
  refine ⟨(1-t)*u+t*v,?_⟩
  intro x hx
  change normalizedPhase ((1-t x)*u x+t x*v x)=φ x
  rcases hx with ha|hb
  · have eq : t x=0 := ta ha
    simpa [eq] using hu x ha
  · have eq : t x=1 := tb hb
    simpa [eq] using hv x hb

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.phase_lifts_in_a_neighborhood
#print axioms TwoAxisHelicoid.clopen_inside_component_neighborhood
