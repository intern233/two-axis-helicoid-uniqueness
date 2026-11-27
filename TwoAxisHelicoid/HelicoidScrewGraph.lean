import TwoAxisHelicoid.HelicoidExteriorGraphCoordinate

namespace TwoAxisHelicoid
open Real Set Filter Bornology Metric
open scoped Topology ContDiff

/-- The screw symmetry of the standard helicoid, in its ambient Cartesian frame. -/
noncomputable def helicoidScrewMove (a : ℝ) (p : HelicoidTubeCoordinates) : HelicoidTubeCoordinates :=
  ((Real.cos a*p.1.1-Real.sin a*p.1.2,Real.sin a*p.1.1+Real.cos a*p.1.2),p.2+a)

theorem helicoidScrewMove_tube (a v r θ : ℝ) :
    helicoidScrewMove a (helicoidTubeMap ((v,r),θ))=helicoidTubeMap ((v,r),θ+a) := by
  ext
  · simp [helicoidScrewMove,helicoidTubeMap,helicoidNormalMap,Real.cos_add,Real.sin_add]
    ring
  · simp [helicoidScrewMove,helicoidTubeMap,helicoidNormalMap,Real.cos_add,Real.sin_add]
    ring
  · simp [helicoidScrewMove,helicoidTubeMap,helicoidNormalMap]
    ring

private theorem helicoidGraphGradientNorm_translate (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) (a : ℝ)
    (diff : DifferentiableAt ℝ u (q-(0,a))) :
    helicoidGraphGradientNorm (fun y => u (y-(0,a))) q=helicoidGraphGradientNorm u (q-(0,a)) := by
  have d : fderiv ℝ (fun y => u (y-(0,a))) q=fderiv ℝ u (q-(0,a)) := by
    have e := diff.hasFDerivAt.comp q ((hasFDerivAt_id q).sub_const (0,a))
    simpa only [id_eq,Function.comp_def,ContinuousLinearMap.comp_id] using e.fderiv
  simp only [helicoidGraphGradientNorm,d,Prod.fst_sub,sub_zero]

/-- Recentring the helicoid by its screw symmetry preserves the full
C¹ end, including cofinality and the decay measured in the induced metric. -/
theorem HasHelicoidC1End.screw_motion {M : Type*} [TopologicalSpace M] [T2Space M]
    {Y : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End Y) (proper : IsProperMap Y) (a : ℝ) :
    HasHelicoidC1End (helicoidScrewMove a ∘ Y) := by
  obtain ⟨d,R,u,hR,dt,ds,large,sm,sp,dec⟩ := graph.exterior_graph_coordinate proper
  let v : ℝ × ℝ := (0,a)
  let B := R+‖v‖+1
  let e := d.trans (Homeomorph.addRight v).toOpenPartialHomeomorph
  have src : e.source=d.source := by ext x; change (x∈d.source ∧ d x∈univ) ↔ _; simp
  have toFun (x : M) : e x=d x+v := rfl
  have invFun (q : ℝ × ℝ) : e.symm q=d.symm (q-v) := by change d.symm (q+ -v)=_; rw [sub_eq_add_neg]
  have old {q : ℝ × ℝ} (h : q∈exteriorPlaneBase B) : q-v∈exteriorPlaneBase R := by
    have le : ‖q‖≤‖q-v‖+‖v‖ := by simpa only [sub_add_cancel] using norm_add_le (q-v) v
    change B<‖q‖ at h
    change R<‖q-v‖
    dsimp [B] at h
    linarith
  have large' : ∀ᶠ x in cocompact M, x∈e.source ∧ e x∈exteriorPlaneBase B := by
    filter_upwards [ds,large.eventually_gt_atTop (B+‖v‖)] with x hx h
    refine ⟨src.symm ▸ hx,?_⟩
    have le : ‖d x‖≤‖d x+v‖+‖v‖ := by simpa only [add_sub_cancel_right] using norm_sub_le (d x+v) v
    change B<‖d x+v‖
    linarith
  have smoothShift : ContDiff ℝ (∞ : WithTop ℕ∞) (fun x : ℝ × ℝ => x-v) := contDiff_id.sub contDiff_const
  have pro : Tendsto (fun x : ℝ × ℝ => x-v) (cobounded (ℝ × ℝ)) (cobounded (ℝ × ℝ)) := by
    rw [Metric.cobounded_eq_cocompact]
    exact (isProperMap_iff_tendsto_cocompact.mp (Homeomorph.addRight (-v)).isProperMap).2
  apply helicoid_graph_of_exterior_chart _ e (R := B) (by dsimp [B]; positivity) _ large' (fun y => u (y-v))
  · exact sm.comp smoothShift.contDiffOn (fun _ h => old h)
  · exact fun q h => (sp _ (old h)).1
  · intro q h
    rw [Function.comp_apply,invFun,(sp _ (old h)).2,helicoidScrewMove_tube]
    simp [v]
  · have eq : ∀ᶠ q in cobounded (ℝ × ℝ), helicoidGraphGradientNorm (fun y => u (y-v)) q=helicoidGraphGradientNorm u (q-v) := by
      filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop B] with q h
      exact helicoidGraphGradientNorm_translate u q a ((sm.contDiffAt ((exteriorPlaneBase_isOpen R).mem_nhds (old h))).differentiableAt (by simp))
    exact (dec.comp pro).congr' (eq.mono fun _ e => congrArg (_+·) e.symm)
  · intro q h
    change q∈univ ∧ q+ -v∈d.target
    exact ⟨mem_univ _,dt.symm ▸ (show q+ -v∈exteriorPlaneBase R from old h)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.screw_motion
