import TwoAxisHelicoid.CompactParameterFiber
import TwoAxisHelicoid.DiskBoundaryArcUniqueness
import Mathlib.Topology.ExtendFrom

namespace TwoAxisHelicoid
open Set Metric Complex Filter Topology
open scoped Topology

/-- In the compact parameter disk, every fiber over a value approached
from locally connected sides is preconnected. The actual inverse disk
map identifies each interior approach with the given planar patch. -/
theorem closed_disk_parameter_fiber_connected {W : Set ℂ} {F : ℂ → ℂ}
    (cf : ContinuousOn F (closedBall 0 1)) (e : complexUnitDisk ≃ₜ W) (rep : ∀ z, (e z).1=F z.1)
    {q : ℂ} (approach : ∀ G : Set ℂ, IsOpen G → q∈G →
      ∃ O : Set ℂ, IsOpen O ∧ q∈O ∧ O⊆G ∧ IsPreconnected (O∩W)) :
    IsPreconnected (closedBall (0:ℂ) 1 ∩ F ⁻¹' {q}) := by
  let K := closedBall (0:ℂ) 1
  let D := (Subtype.val : K → ℂ) ⁻¹' complexUnitDisk
  let i : complexUnitDisk → K := fun x => ⟨x.1,ball_subset_closedBall x.2⟩
  let u := fun x : K => F x.1
  have cu : Continuous u := continuousOn_iff_continuous_domRestrict.mp cf
  have dense : Dense D := by
    intro x
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    change x.1∈closure ((Subtype.val : K → ℂ) '' D)
    rw [show (Subtype.val : K → ℂ) '' D=complexUnitDisk from
      (Subtype.image_preimage_coe K complexUnitDisk).trans (inter_eq_right.mpr ball_subset_closedBall),
      show closure complexUnitDisk=K from closure_ball (0:ℂ) (one_ne_zero : (1:ℝ)≠0)]
    exact x.2
  have sides (G : Set ℂ) (og : IsOpen G) (qg : q∈G) :
      ∃ O : Set ℂ, IsOpen O ∧ q∈O ∧ O⊆G ∧ IsPreconnected (D ∩ u ⁻¹' O) := by
    obtain ⟨O,oo,qo,sub,conn⟩ := approach G og qg
    let S := (Subtype.val : W → ℂ) ⁻¹' O
    have cs : IsPreconnected S := Topology.IsInducing.subtypeVal.isPreconnected_image.mp (by
      rw [show (Subtype.val : W → ℂ) '' S=O∩W from (Subtype.image_preimage_coe W O).trans (inter_comm _ _)]
      exact conn)
    have eq : (i ∘ e.symm) '' S=D∩u ⁻¹' O := by
      ext x
      constructor
      · rintro ⟨v,sv,rfl⟩
        refine ⟨(e.symm v).2,?_⟩
        change F (e.symm v).1∈O
        rw [← rep,e.apply_symm_apply]
        exact sv
      · rintro ⟨xd,xo⟩
        let z : complexUnitDisk := ⟨x.1,xd⟩
        refine ⟨e z,?_,?_⟩
        · change (e z).1∈O
          rwa [rep]
        · change i (e.symm (e z))=x
          rw [e.symm_apply_apply]
    refine ⟨O,oo,qo,sub,eq ▸ cs.image _ ?_⟩
    exact ((continuous_subtype_val.subtype_mk _ : Continuous i).comp e.symm.continuous).continuousOn
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) 1)
  have fiber := connected_fiber_of_connected_approaches cu dense sides
  have eq : (Subtype.val : K → ℂ) '' (u ⁻¹' {q})=K∩F ⁻¹' {q} := by
    ext z
    exact ⟨fun ⟨w,h,eq⟩ => eq ▸ ⟨w.2,h⟩,fun ⟨inK,h⟩ => ⟨⟨z,inK⟩,h,rfl⟩⟩
  rw [← eq]
  exact fiber.image _ continuous_subtype_val.continuousOn

/-- Compactification of a univalent disk parameter with continuous
boundary limits and connected interior sides. The absence of a collapsed
boundary arc follows from the maximum modulus principle. -/
theorem closed_disk_homeomorph_of_circle_limits {W : Set ℂ} (ow : IsOpen W) {f : ℂ → ℂ}
    (an : AnalyticOnNhd ℂ f complexUnitDisk) (e : complexUnitDisk ≃ₜ W) (rep : ∀ z, (e z).1=f z.1)
    (sides : ∀ q∈closure W, ∀ G : Set ℂ, IsOpen G → q∈G →
      ∃ O : Set ℂ, IsOpen O ∧ q∈O ∧ O⊆G ∧ IsPreconnected (O∩W))
    (limits : ∀ ζ : ℂ, ‖ζ‖=1 → ∃ q∈closure W, Tendsto f (𝓝[complexUnitDisk] ζ) (𝓝 q)) :
    ∃ H : closedBall (0:ℂ) 1 ≃ₜ closure W, ∀ z, z.1∈complexUnitDisk ↔ (H z).1∈W := by
  classical
  let D := complexUnitDisk
  let K := closedBall (0:ℂ) 1
  let F := extendFrom D f
  have cl : closure D=K := closure_ball (0:ℂ) (one_ne_zero : (1:ℝ)≠0)
  have extension {z : ℂ} (hz : z∈K) : ∃ q∈closure W, Tendsto f (𝓝[D] z) (𝓝 q) := by
    rcases (mem_closedBall_zero_iff.mp hz).lt_or_eq with inside|boundary
    · have h : z∈D := mem_ball_zero_iff.mpr inside
      exact ⟨f z,subset_closure (rep ⟨z,h⟩ ▸ (e ⟨z,h⟩).2),(an _ h).continuousAt.continuousWithinAt⟩
    · exact limits z boundary
  have cf : ContinuousOn F K := continuousOn_extendFrom cl.symm.subset (fun _ h => by
    obtain ⟨q,_,t⟩ := extension h; exact ⟨q,t⟩)
  have same {z : ℂ} (hz : z∈D) : F z=f z := extendFrom_eq (subset_closure hz) (an _ hz).continuousAt.continuousWithinAt
  have joined (z : D) : (e z).1=F z.1 := (rep z).trans (same z.2).symm
  have cod {z : ℂ} (hz : z∈K) : F z∈closure W := by
    obtain ⟨w,hw,t⟩ := extension hz
    change extendFrom D f z∈closure W
    rw [extendFrom_eq (cl.symm ▸ hz) t]
    exact hw
  have image : F '' K=closure W := by
    refine Subset.antisymm (fun _ h => ?_) ?_
    · obtain ⟨z,hz,rfl⟩ := h
      exact cod hz
    apply closure_minimal _ ((isCompact_closedBall (0:ℂ) 1).image_of_continuousOn cf).isClosed
    intro w hw
    let z := e.symm ⟨w,hw⟩
    exact ⟨z.1,ball_subset_closedBall z.2,(joined z).symm.trans (congrArg Subtype.val (e.apply_symm_apply _))⟩
  let g := fun z : ℂ => if hz : z∈W then (e.symm ⟨z,hz⟩).1 else 0
  have cg : ContinuousOn g W := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have eq : W.domRestrict g=Subtype.val ∘ e.symm := by funext z; simp [g,z.2]
    rw [eq]
    exact continuous_subtype_val.comp e.symm.continuous
  have identity {z : ℂ} (hz : z∈D) : g (f z)=z := by
    let x : D := ⟨z,hz⟩
    change g (f x.1)=x.1
    rw [← rep x]
    simp [g,(e x).2]
  have back {z : ℂ} (hz : z∈K) (inW : F z∈W) : z=g (F z) ∧ z∈D := by
    have zz : z∈closure D := cl.symm ▸ hz
    let _ := mem_closure_iff_nhdsWithin_neBot.mp zz
    have tend := tendsto_extendFrom (f:=f) (A:=D) (x:=z) (by obtain ⟨q,_,t⟩ := extension hz; exact ⟨q,t⟩)
    have idt : Tendsto (g ∘ f) (𝓝[D] z) (𝓝 z) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).congr' (Filter.mem_of_superset self_mem_nhdsWithin fun _ h => (identity h).symm)
    have eq := tendsto_nhds_unique idt ((cg.continuousAt (ow.mem_nhds inW)).tendsto.comp tend)
    have mem : g (F z)∈D := by
      change (if hw : F z∈W then (e.symm ⟨F z,hw⟩).1 else 0)∈D
      rw [dite_eq_left inW]
      exact (e.symm ⟨F z,inW⟩).2
    exact ⟨eq,eq.symm ▸ mem⟩
  have inject : InjOn F K := by
    intro x hx y hy eq
    by_cases inW : F x∈W
    · exact (back hx inW).1.trans ((congrArg g eq).trans (back hy (eq ▸ inW)).1.symm)
    by_contra distinct
    let S := K∩F ⁻¹' {F x}
    have xs : x∈S := ⟨hx,rfl⟩
    have ys : y∈S := ⟨hy,eq.symm⟩
    have circle : S⊆sphere 0 1 := by
      rintro z ⟨zk,hit⟩
      apply mem_sphere_zero_iff_norm.mpr
      refine (mem_closedBall_zero_iff.mp zk).eq_of_not_lt ?_
      intro small
      have d : z∈D := mem_ball_zero_iff.mpr small
      exact inW ((show F z=F x from hit) ▸ (joined ⟨z,d⟩ ▸ (e ⟨z,d⟩).2))
    have connected := closed_disk_parameter_fiber_connected cf e joined (sides (F x) (cod hx))
    obtain ⟨O,oo,marked,contains⟩ := circle_continuum_contains_arc circle connected xs ys distinct
    have aF : AnalyticOnNhd ℂ F D := by
      intro z hz
      exact (an z hz).congr (Filter.mem_of_superset (isOpen_ball.mem_nhds hz) fun w hw => (same hw).symm)
    have zero := disk_arc_zero_at_center (f:=fun z => F z-F x) (fun z hz => (aF z hz).sub analyticAt_const)
      (cf.sub continuousOn_const) oo marked (fun z h => sub_eq_zero.mpr (contains h).2)
    have atZero : (0:ℂ)∈D := mem_ball_self zero_lt_one
    exact inW ((sub_eq_zero.mp zero) ▸ (joined ⟨0,atZero⟩ ▸ (e ⟨0,atZero⟩).2))
  let u := fun x : K => (⟨F x.1,cod x.2⟩:closure W)
  have bij : Function.Bijective u := ⟨fun x y eq => Subtype.ext (inject x.2 y.2 (congrArg Subtype.val eq)),by
    intro w; obtain ⟨x,hx,eq⟩ := (show w.1∈F '' K from image.symm ▸ w.2); exact ⟨⟨x,hx⟩,Subtype.ext eq⟩⟩
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) 1)
  let equiv := Equiv.ofBijective u bij
  have cu : Continuous equiv := (continuousOn_iff_continuous_domRestrict.mp cf).subtype_mk _
  refine ⟨cu.homeoOfEquivCompactToT2,fun z => ?_⟩
  change z.1∈D ↔ F z.1∈W
  exact ⟨fun hz => (joined ⟨z.1,hz⟩) ▸ (e ⟨z.1,hz⟩).2,fun hz => (back z.2 hz).2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.closed_disk_parameter_fiber_connected
#print axioms TwoAxisHelicoid.closed_disk_homeomorph_of_circle_limits
