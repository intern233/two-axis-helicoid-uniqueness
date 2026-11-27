import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

/-- The constants of integration, with the discrete topology used for
analytic continuation of primitive germs. -/
private structure PrimitiveConstant where
  value : ℂ

private instance : TopologicalSpace PrimitiveConstant := ⊥
private instance : DiscreteTopology PrimitiveConstant := ⟨rfl⟩

/-- Local complex-valued primitives whose pairwise differences are
locally constant glue up to additive constants on a simply connected
base. The proof constructs the covering of primitive germs. -/
theorem simply_connected_glue_local_primitives {B ι : Type*} [TopologicalSpace B]
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B] (b : B)
    (U : ι → Set B) (op : ∀ i, IsOpen (U i)) (index : B → ι) (cover : ∀ x, x∈U (index x))
    (f : ι → B → ℂ)
    (overlap : ∀ i j x, x∈U i∩U j → ∀ᶠ y in 𝓝 x, f i y-f j y=f i x-f j x) :
    ∃ F : B → ℂ, ∀ i x, x∈U i → ∀ᶠ y in 𝓝 x, F y-f i y=F x-f i x := by
  let C : FiberBundleCore ι B PrimitiveConstant := {
    baseSet := U
    isOpen_baseSet := op
    indexAt := index
    mem_baseSet_at := cover
    coordChange := fun i j x v => ⟨v.value+(f i x-f j x)⟩
    coordChange_self := by intro i x hx v; cases v; simp
    continuousOn_coordChange := by
      intro i j p hp
      apply ContinuousAt.continuousWithinAt
      apply continuousAt_const.congr_of_eventuallyEq
      have same := (continuous_fst.continuousAt (x := p)).tendsto.eventually (overlap i j p.1 hp.1)
      have fiber : ∀ᶠ q : B × PrimitiveConstant in 𝓝 p, q.2=p.2 :=
        continuous_snd.continuousAt.tendsto.eventually (isOpen_discrete ({p.2} : Set PrimitiveConstant) |>.mem_nhds rfl)
      filter_upwards [same,fiber] with q h hq
      change PrimitiveConstant.mk (q.2.value+(f i q.1-f j q.1))=PrimitiveConstant.mk (p.2.value+(f i p.1-f j p.1))
      rw [h,hq]
    coordChange_comp := by intro i j k x hx v; congr 1; ring }
  have cov : IsCoveringMap C.proj := FiberBundle.isCoveringMap
  obtain ⟨s,⟨_,eq⟩,_⟩ := cov.existsUnique_continuousMap_lifts (ContinuousMap.id B) b (⟨b,⟨0⟩⟩ : C.TotalSpace) rfl
  have base (x : B) : (s x).1=x := congrFun eq x
  let F := fun x => f (index (s x).1) (s x).1+(s x).2.value
  refine ⟨F,?_⟩
  intro i x hx
  let T := C.localTriv i
  have source : s x∈T.source := (C.mem_localTriv_source i _).mpr (by change (s x).1∈U i; rwa [base])
  have cont : ContinuousAt (fun y => (T (s y)).2) x :=
    continuous_snd.continuousAt.comp (T.continuousAt source |>.comp s.continuous.continuousAt)
  have const : ∀ᶠ y in 𝓝 x, (T (s y)).2=(T (s x)).2 :=
    cont.tendsto.eventually ((isOpen_discrete ({(T (s x)).2} : Set PrimitiveConstant)).mem_nhds rfl)
  have form (y : B) : (T (s y)).2.value=F y-f i y := by
    change (s y).2.value+(f (index (s y).1) (s y).1-f i (s y).1)=f (index (s y).1) (s y).1+(s y).2.value-f i y
    rw [base]
    abel
  filter_upwards [const] with y hy
  exact (form y).symm.trans ((congrArg PrimitiveConstant.value hy).trans (form x))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.simply_connected_glue_local_primitives
