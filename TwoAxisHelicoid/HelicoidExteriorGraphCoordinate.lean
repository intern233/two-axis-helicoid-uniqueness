import TwoAxisHelicoid.HelicoidGraphChartCriterion

namespace TwoAxisHelicoid
open Set Filter Bornology Metric
open scoped Topology ContDiff

/-- In a proper C¹ end the given graph parametrization extends to an
open chart with cofinal source. Its base escapes all bounded sets on
the surface end and its global scalar extension has decaying gradient. -/
theorem HasHelicoidC1End.exterior_graph_coordinate {M : Type*} [TopologicalSpace M] [T2Space M]
    {Y : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End Y) (proper : IsProperMap Y) :
    ∃ (e : OpenPartialHomeomorph M (ℝ × ℝ)) (R : ℝ) (u : ℝ × ℝ → ℝ), 0<R ∧
      e.target=exteriorPlaneBase R ∧ e.source∈cocompact M ∧
      Tendsto (fun x => ‖e x‖) (cocompact M) atTop ∧
      ContDiffOn ℝ (∞ : WithTop ℕ∞) u (exteriorPlaneBase R) ∧
      (∀ q∈exteriorPlaneBase R, |u q|≤1/2 ∧ Y (e.symm q)=helicoidTubeMap ((u q,q.1),q.2)) ∧
      Tendsto (fun q => |u q|+helicoidGraphGradientNorm u q) (cobounded (ℝ × ℝ)) (𝓝 0) := by
  classical
  obtain ⟨C,_,R,hR,core,E,_,u,sm,sp,decay⟩ := graph
  let S := helicoidProjectedEnd Y C (exteriorPlaneBase R)
  let T := exteriorPlaneBase R
  have nonT : Nonempty T := ⟨⟨(0,R+1),by
    change R<‖((0:ℝ),R+1)‖
    have bd := norm_snd_le ((0:ℝ),R+1)
    change ‖R+1‖≤‖((0:ℝ),R+1)‖ at bd
    rw [Real.norm_eq_abs,abs_of_pos (by linarith : 0<R+1)] at bd
    exact (lt_add_one R).trans_le bd⟩⟩
  have os : IsOpen S := by simpa only [compl_compl] using core.isClosed.isOpen_compl
  obtain ⟨e,src,tgt,ef⟩ := open_coordinate_of_subsets os (exteriorPlaneBase_isOpen R) (nonT.map E.symm) E
  let U := extendOpenScalar u
  have val (q : T) : U q.1=u q := by
    unfold U extendOpenScalar
    split_ifs with h
    · rfl
    · exact False.elim (h q.2)
  have shape (q : T) : |U q.1|≤1/2 ∧ Y (e.symm q.1)=helicoidTubeMap ((U q.1,q.1.1),q.1.2) := by
    have eq : e (E.symm q).1=q.1 := (ef _).trans (congrArg Subtype.val (E.apply_symm_apply q))
    have back : e.symm q.1=(E.symm q).1 := eq ▸ (e.left_inv (src.symm ▸ (E.symm q).2))
    rw [back,val]
    exact sp q
  have tail : e.source∈cocompact M := by rw [src]; simpa only [compl_compl] using core.compl_mem_cocompact
  have esc := tendsto_norm_cocompact_atTop.comp (isProperMap_iff_tendsto_cocompact.mp proper).2
  have limit : Tendsto (fun x => ‖e x‖) (cocompact M) atTop := by
    refine tendsto_atTop.mpr fun a => ?_
    let A := closedBall (0 : ℝ × ℝ) a
    obtain ⟨b,bd⟩ := (helicoidHeightBlock_isCompact (1/2) (isCompact_closedBall (0 : ℝ × ℝ) a)).isBounded.exists_norm_le
    filter_upwards [tail,esc.eventually_gt_atTop b] with x hx large
    by_contra! h
    have q : e x∈T := by change e x∈exteriorPlaneBase R; rw [← tgt]; exact e.map_source hx
    obtain ⟨small,sh⟩ := shape ⟨e x,q⟩
    rw [e.left_inv hx] at sh
    have box : Y x∈helicoidHeightBlock (1/2) A :=
      ⟨(U (e x),e x),⟨abs_le.mp small,by simpa only [A,mem_closedBall,dist_zero_right] using h.le⟩,sh.symm⟩
    exact large.not_ge (bd _ box)
  refine ⟨e,R,U,hR,tgt,tail,limit,sm,fun q h => shape ⟨q,h⟩,?_⟩
  have ext : T∈cobounded (ℝ × ℝ) := tendsto_norm_cobounded_atTop.eventually_gt_atTop R
  have eqMap : map (Subtype.val : T → ℝ × ℝ) (comap Subtype.val (cobounded (ℝ × ℝ)))=cobounded (ℝ × ℝ) :=
    map_comap_of_mem (by simpa only [Subtype.range_coe] using ext)
  rw [← eqMap]
  apply tendsto_map'_iff.mpr
  exact decay.congr fun q => by simp only [Function.comp_apply,val,U]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.exterior_graph_coordinate
