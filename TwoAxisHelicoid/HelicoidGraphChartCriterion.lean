import TwoAxisHelicoid.HelicoidHeightDecayStraightening
import TwoAxisHelicoid.HelicoidGraphExteriorMetric
import TwoAxisHelicoid.OpenSubsetCoordinate

namespace TwoAxisHelicoid
open Set Filter Bornology Metric
open scoped Topology ContDiff

/-- A graph on an end chart gives the actual compact complement and
the actual normal projection required by the single-sheeted C¹ end. -/
theorem helicoid_graph_of_exterior_chart {M : Type*} [TopologicalSpace M] [T2Space M]
    (Y : M → HelicoidTubeCoordinates) (e : OpenPartialHomeomorph M (ℝ × ℝ)) {R : ℝ} (hR : 0<R)
    (outer : exteriorPlaneBase R⊆e.target)
    (endMem : ∀ᶠ x in cocompact M, x∈e.source ∧ e x∈exteriorPlaneBase R)
    (u : ℝ × ℝ → ℝ) (smooth : ContDiffOn ℝ (∞ : WithTop ℕ∞) u (exteriorPlaneBase R))
    (small : ∀ q∈exteriorPlaneBase R, |u q|≤1/2)
    (shape : ∀ q∈exteriorPlaneBase R, Y (e.symm q)=helicoidTubeMap ((u q,q.1),q.2))
    (decay : Tendsto (fun q => |u q|+helicoidGraphGradientNorm u q) (cobounded (ℝ × ℝ)) (𝓝 0)) :
    HasHelicoidC1End Y := by
  classical
  let T := exteriorPlaneBase R
  let D := e.source ∩ e ⁻¹' T
  have op : IsOpen D := e.continuousOn.isOpen_inter_preimage e.open_source (exteriorPlaneBase_isOpen R)
  have ev : D∈cocompact M := endMem
  obtain ⟨K,hK,sub⟩ := mem_cocompact'.mp ev
  have compact : IsCompact Dᶜ := hK.of_isClosed_subset op.isClosed_compl sub
  let V := helicoidProjectedEnd Y Dᶜ T
  have coord (x : M) (hx : x∈D) : helicoidBaseCoordinates (Y x)=e x := by
    obtain ⟨src,large⟩ := hx
    rw [← e.left_inv src,shape (e x) large,e.right_inv (e.map_source src)]
    exact normal_graph_coordinates_exact ((small _ large).trans_lt (by norm_num)) _
  have eq (x : M) : x∈V ↔ x∈D := by
    change (x∉Dᶜ ∧ helicoidBaseCoordinates (Y x)∈T) ↔ x∈D
    simp only [notMem_compl_iff]
    exact ⟨And.left,fun h => ⟨h,(coord x h).symm ▸ h.2⟩⟩
  let f : V → T := fun x => ⟨e x.1,((eq x.1).mp x.2).2⟩
  let g : T → V := fun q => ⟨e.symm q.1,(eq _).mpr ⟨e.map_target (outer q.2),
    by change e (e.symm q.1)∈T; rw [e.right_inv (outer q.2)]; exact q.2⟩⟩
  let U : V ≃ₜ T :=
    { toFun := f
      invFun := g
      left_inv := fun x => Subtype.ext (e.left_inv ((eq x.1).mp x.2).1)
      right_inv := fun q => Subtype.ext (e.right_inv (outer q.2))
      continuous_toFun := Continuous.subtype_mk (continuous_iff_continuousAt.mpr fun x : V =>
        (e.continuousAt ((eq x.1).mp x.2).1).comp continuous_subtype_val.continuousAt) _
      continuous_invFun := Continuous.subtype_mk (continuous_iff_continuousAt.mpr fun q : T =>
        (e.symm.continuousAt (outer q.2)).comp continuous_subtype_val.continuousAt) _ }
  let v : T → ℝ := fun q => u q.1
  have same (q : ℝ × ℝ) (hq : q∈T) : extendOpenScalar v =ᶠ[𝓝 q] u := by
    filter_upwards [(exteriorPlaneBase_isOpen R).mem_nhds hq] with y hy
    change (if _ : y ∈ T then u y else 0) = u y
    split
    · rfl
    · rename_i outside
      exact (outside (show y∈T from hy)).elim
  refine ⟨Dᶜ,compact,R,hR,?_,U,?_,v,?_,?_,?_⟩
  · change IsCompact Vᶜ
    rw [show V=D from Set.ext eq]
    exact compact
  · exact funext fun x => Subtype.ext (coord x.1 ((eq x.1).mp x.2)).symm
  · exact fun q hq => (smooth q hq).congr_of_eventuallyEq ((same q hq).filter_mono nhdsWithin_le_nhds) (same q hq).self_of_nhds
  · intro q
    exact ⟨small _ q.2,shape _ q.2⟩
  · have d := decay.comp (tendsto_comap : Tendsto (Subtype.val : T → ℝ × ℝ) (comap Subtype.val (cobounded (ℝ × ℝ))) (cobounded (ℝ × ℝ)))
    apply d.congr
    intro q
    simp only [Function.comp_apply,v,helicoidGraphGradientNorm,(same q.1 q.2).fderiv_eq]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoid_graph_of_exterior_chart
