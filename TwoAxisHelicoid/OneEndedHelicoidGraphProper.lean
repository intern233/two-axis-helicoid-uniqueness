import TwoAxisHelicoid.HelicoidHeightDecayStraightening
import TwoAxisHelicoid.HelicoidGraphEscape
import TwoAxisHelicoid.ExteriorHeightEscape
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

namespace TwoAxisHelicoid
open Set Filter Metric Bornology Topology
open scoped Topology ContDiff

/-- On a surface with one end, a single exterior helicoidal graph with
bounded height already forces its parameter to go to infinity on the
genuine end. The boundary of a larger base disk lifts to a compact
separator on the given surface. -/
theorem one_ended_graph_parameter_escapes {M : Type*} [TopologicalSpace M] [T2Space M]
    {X : M → HelicoidTubeCoordinates} (cx : Continuous X) (tail : HasConnectedCompactTails M)
    {S : Set M} (core : IsCompact Sᶜ) {R : ℝ} (E : S ≃ₜ exteriorPlaneBase R)
    (u : exteriorPlaneBase R → ℝ) (bound : ∀ b, |u b|≤1/2)
    (graph : ∀ q : S, X q.1=helicoidTubeMap ((u (E q),(E q).1.1),(E q).1.2)) :
    Tendsto (fun x => ‖helicoidBaseCoordinates (X x)‖) (cocompact M) atTop := by
  let p := helicoidBaseCoordinates ∘ X
  have agrees (q : S) : p q.1=(E q).1 := by
    change helicoidBaseCoordinates (X q.1)=_
    rw [graph q]
    exact normal_graph_coordinates_exact ((bound _).trans_lt (by norm_num)) _
  have cp : ContinuousOn p S := continuousOn_iff_continuous_domRestrict.mpr
    ((continuous_subtype_val.comp E.continuous).congr (fun q => (agrees q).symm))
  have inverse (b : exteriorPlaneBase R) : X (E.symm b).1=helicoidTubeMap ((u b,b.1.1),b.1.2) := by
    simpa only [E.apply_symm_apply] using graph (E.symm b)
  apply Filter.tendsto_atTop.mpr
  intro A
  let ρ := max A R+1
  have ar : A<ρ := by dsimp [ρ]; linarith [le_max_left A R]
  have rr : R<ρ := by dsimp [ρ]; linarith [le_max_right A R]
  let B := {q : exteriorPlaneBase R | ‖q.1‖=ρ}
  have compact : IsCompact B := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have eq : Subtype.val '' B=Metric.sphere (0:ℝ × ℝ) ρ := by
      ext w
      constructor
      · rintro ⟨v,hv,rfl⟩
        simpa only [Metric.mem_sphere,dist_zero_right] using (show ‖v.1‖=ρ from hv)
      · intro hw
        have val : ‖w‖=ρ := by simpa only [Metric.mem_sphere,dist_zero_right] using hw
        exact ⟨⟨w,show R<‖w‖ by rwa [val]⟩,val,rfl⟩
    rw [eq]
    exact isCompact_sphere _ _
  let lift := fun b : exteriorPlaneBase R => (E.symm b).1
  let K := lift '' B
  have kc : IsCompact K := compact.image (continuous_subtype_val.comp E.symm.continuous)
  obtain ⟨U,connected,covered,off⟩ := tail _ (core.union kc)
  have included : U⊆S := fun q hq => by
    by_contra hn
    exact disjoint_left.mp off hq (Or.inl hn)
  have avoid (q) (hq : q∈U) : ‖p q‖≠ρ := by
    intro eq
    let v : S := ⟨q,included hq⟩
    have eb : E v∈B := by change ‖(E v).1‖=ρ; rw [← agrees]; exact eq
    exact disjoint_left.mp off hq (Or.inr ⟨E v,eb,congrArg Subtype.val (E.symm_apply_apply v)⟩)
  let T := (fun x => ‖p x‖) '' U
  have ct : IsPreconnected T := connected.image _ (cp.norm.mono included)
  have gap : T⊆Iio ρ ∪ Ioi ρ := by
    rintro _ ⟨q,hq,rfl⟩
    exact lt_or_gt_of_ne (avoid q hq)
  obtain ⟨D,_,far⟩ := helicoid_graph_inverse_avoids_compact cx (Y:=lift)
    (u:=u) (fun b => (bound b).trans (by norm_num)) inverse covered
  let s := max 0 (max D ρ)+1
  have sp : 0<s := by dsimp [s]; linarith [le_max_left (0:ℝ) (max D ρ)]
  have ds : D<s := by dsimp [s]; linarith [le_max_left D ρ,le_max_right (0:ℝ) (max D ρ)]
  have rs : ρ<s := by dsimp [s]; linarith [le_max_right D ρ,le_max_right (0:ℝ) (max D ρ)]
  have ss : ‖(s,(0:ℝ))‖=s := by simp [Prod.norm_def,Real.norm_eq_abs,abs_of_pos sp,sp.le]
  let b : exteriorPlaneBase R := ⟨(s,0),show R<‖(s,(0:ℝ))‖ by rw [ss]; exact rr.trans rs⟩
  have big : lift b∈U := not_not.mp (far b (ss ▸ ds))
  have val : ‖p (lift b)‖=s := by rw [agrees (E.symm b),E.apply_symm_apply]; exact ss
  rcases ct.subset_or_subset isOpen_Iio isOpen_Ioi (disjoint_left.mpr fun _ l h => (l : _<ρ).asymm h) gap with small|large
  · exact False.elim (rs.not_gt (val ▸ (small (mem_image_of_mem _ big) : ‖p (lift b)‖<ρ)))
  · have nb : U∈cocompact M := by simpa only [compl_compl] using covered.compl_mem_cocompact
    filter_upwards [nb] with x hx
    exact ar.le.trans (large (mem_image_of_mem _ hx) : ρ<‖p x‖).le

/-- A continuous one-ended bounded-height graph is proper in space.
The proof does not require a curvature estimate. -/
theorem HasHelicoidHeightEnd.proper_of_one_end {M : Type*} [TopologicalSpace M] [T2Space M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidHeightEnd X) (cx : Continuous X)
    (tail : HasConnectedCompactTails M) : IsProperMap X := by
  obtain ⟨S,core,R,_,E,u,_,bound,formula,_⟩ := graph
  have esc := one_ended_graph_parameter_escapes cx tail core E u bound formula
  apply isProperMap_iff_tendsto_cocompact.mpr
  refine ⟨cx,?_⟩
  rw [← Metric.cobounded_eq_cocompact]
  apply tendsto_norm_atTop_iff_cobounded.mp
  apply Filter.tendsto_atTop.mpr
  intro b
  have nb : S∈cocompact M := by simpa only [compl_compl] using core.compl_mem_cocompact
  filter_upwards [nb,esc.eventually_ge_atTop (2*b+1)] with x hx large
  let q : S := ⟨x,hx⟩
  rw [formula q,normal_graph_coordinates_exact ((bound _).trans_lt (by norm_num))] at large
  have cmp := helicoid_normal_parameters_norm_bound (E q).1.1 (E q).1.2 (u (E q)) ((bound _).trans (by norm_num))
  change b≤‖X q.1‖
  rw [formula q]
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.one_ended_graph_parameter_escapes
#print axioms TwoAxisHelicoid.HasHelicoidHeightEnd.proper_of_one_end
