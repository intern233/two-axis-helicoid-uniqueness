import TwoAxisHelicoid.SimplyConnectedLocalPrimitives
import Mathlib.Analysis.Complex.Circle

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

private structure DiscreteUnitaryPhase where
  value : Circle

private instance : TopologicalSpace DiscreteUnitaryPhase := ⊥
private instance : DiscreteTopology DiscreteUnitaryPhase := ⟨rfl⟩

/-- Local complex functions on a simply connected base glue after
multiplication by unit constants whenever the transition is unique as
a germ. Common isolated zeros are allowed. -/
theorem simply_connected_glue_unitary_germs {B ι : Type*} [TopologicalSpace B]
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B] (p : B)
    (U : ι → Set B) (op : ∀ i, IsOpen (U i)) (index : B → ι) (cover : ∀ x, x∈U (index x))
    (f : ι → B → ℂ) (overlap : ∀ i j x, x∈U i∩U j →
      ∃! c : Circle, ∀ᶠ y in 𝓝 x, f i y=(c:ℂ)*f j y) :
    ∃ F : B → ℂ, ∀ i x, x∈U i → ∃ c : Circle, ∀ᶠ y in 𝓝 x, F y=(c:ℂ)*f i y := by
  classical
  let C := fun i j x => if h : x∈U i∩U j then (overlap i j x h).choose else (1:Circle)
  have form (i j : ι) (x : B) (hx : x∈U i∩U j) :
      ∀ᶠ y in 𝓝 x, f i y=(C i j x:ℂ)*f j y := by
    simpa only [C,dite_eq_left hx] using (overlap i j x hx).choose_spec.1
  have unique (i j : ι) (x : B) (hx : x∈U i∩U j) (c : Circle)
      (h : ∀ᶠ y in 𝓝 x, f i y=(c:ℂ)*f j y) : c=C i j x := by
    exact (overlap i j x hx).unique h (form i j x hx)
  have locally (i j : ι) (x : B) (hx : x∈U i∩U j) : ∀ᶠ y in 𝓝 x, C i j y=C i j x := by
    filter_upwards [((op i).inter (op j)).mem_nhds hx,(form i j x hx).eventually_nhds] with y hy h
    exact (unique i j y hy _ h).symm
  have self (i : ι) (x : B) (hx : x∈U i) : C i i x=1 := by
    apply (unique i i x ⟨hx,hx⟩ 1 ?_).symm
    simp
  have cocycle (i j k : ι) (x : B) (hx : x∈U i∩U j∩U k) : C i j x*C j k x=C i k x := by
    apply unique i k x ⟨hx.1.1,hx.2⟩
    filter_upwards [form i j x hx.1,form j k x ⟨hx.1.2,hx.2⟩] with y h g
    rw [h,g,Circle.coe_mul,mul_assoc]
  let A : FiberBundleCore ι B DiscreteUnitaryPhase := {
    baseSet := U, isOpen_baseSet := op, indexAt := index, mem_baseSet_at := cover,
    coordChange := fun i j x v => ⟨v.value*C i j x⟩
    coordChange_self := by intro i x hx v; cases v; simp [self i x hx]
    continuousOn_coordChange := by
      intro i j a ha
      apply ContinuousAt.continuousWithinAt
      apply continuousAt_const.congr_of_eventuallyEq
      have lc := (continuous_fst.continuousAt (x:=a)).tendsto.eventually (locally i j a.1 ha.1)
      have fc : ∀ᶠ q : B × DiscreteUnitaryPhase in 𝓝 a, q.2=a.2 :=
        continuous_snd.continuousAt.tendsto.eventually ((isOpen_discrete ({a.2} : Set DiscreteUnitaryPhase)).mem_nhds rfl)
      filter_upwards [lc,fc] with q h hq
      change DiscreteUnitaryPhase.mk (q.2.value*C i j q.1)=DiscreteUnitaryPhase.mk (a.2.value*C i j a.1)
      rw [h,hq]
    coordChange_comp := by intro i j k x hx v; congr 1; rw [mul_assoc,cocycle i j k x hx] }
  have proj : IsCoveringMap A.proj := FiberBundle.isCoveringMap
  obtain ⟨s,⟨_,eq⟩,_⟩ := proj.existsUnique_continuousMap_lifts (ContinuousMap.id B) p (⟨p,⟨1⟩⟩ : A.TotalSpace) rfl
  have base (x : B) : (s x).1=x := congrFun eq x
  let F := fun x => ((s x).2.value:ℂ)*f (index (s x).1) (s x).1
  refine ⟨F,?_⟩
  intro i x hx
  let T := A.localTriv i
  have source : s x∈T.source := (A.mem_localTriv_source i _).mpr (by change (s x).1∈U i; rwa [base])
  have cont : ContinuousAt (fun y => (T (s y)).2) x :=
    continuous_snd.continuousAt.comp ((T.continuousAt source).comp s.continuous.continuousAt)
  have same := cont.tendsto.eventually ((isOpen_discrete ({(T (s x)).2} : Set DiscreteUnitaryPhase)).mem_nhds rfl)
  refine ⟨(T (s x)).2.value,?_⟩
  filter_upwards [same,(op i).mem_nhds hx] with y hy yi
  have hval : (T (s y)).2.value=(s y).2.value*C (index (s y).1) i (s y).1 := rfl
  rw [show (T (s x)).2=(T (s y)).2 from hy.symm,hval,Circle.coe_mul,mul_assoc]
  change ((s y).2.value:ℂ)*f (index (s y).1) (s y).1=_
  rw [base]
  rw [(form (index y) i y ⟨cover y,yi⟩).self_of_nhds]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.simply_connected_glue_unitary_germs
