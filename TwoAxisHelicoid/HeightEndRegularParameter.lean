import TwoAxisHelicoid.HelicoidNaturalPuncture
import TwoAxisHelicoid.HelicoidHeightDecayStraightening
import TwoAxisHelicoid.HelicoidHeightGraphTangents
import TwoAxisHelicoid.CoordinateTubeHomeomorph

namespace TwoAxisHelicoid
open Complex Filter Set Bornology Metric Topology
open scoped Topology ContDiff

/-- The actual exterior graph of a height-decaying end provides an
ordinary planar chart. Its centers escape in the conformal parameter
of the base helicoid even before estimating any slope. -/
theorem HasHelicoidHeightEnd.physical_parameter {M : Type*} [TopologicalSpace M] [T2Space M]
    {X : M → Fin 3 → ℝ} (graph : HasHelicoidHeightEnd (coordinateToTube ∘ X)) (proper : IsProperMap X) :
    ∃ (e : OpenPartialHomeomorph M ℂ) (u : ℝ × ℝ → ℝ),
      e.source∈cocompact M ∧ e.target∈cobounded ℂ ∧ Tendsto (fun x => ‖e x‖) (cocompact M) atTop ∧
      ∀ z∈e.target, ContDiffAt ℝ ∞ u (helicoidConformalBase z) ∧ |u (helicoidConformalBase z)|≤1/2 ∧
        (X ∘ e.symm) z=helicoidHeightSurface u z := by
  classical
  let Y := coordinateToTube ∘ X
  obtain ⟨S,core,R,rp,E,u,smooth,bound,formula,_⟩ := graph
  let T := exteriorPlaneBase R
  have nonT : Nonempty T := ⟨⟨(0,R+1),by
    change R<‖((0:ℝ),R+1)‖
    have bd := norm_snd_le ((0:ℝ),R+1)
    change ‖R+1‖≤‖((0:ℝ),R+1)‖ at bd
    rw [Real.norm_eq_abs,abs_of_pos (by linarith : 0<R+1)] at bd
    exact (lt_add_one R).trans_le bd⟩⟩
  have os : IsOpen S := by simpa only [compl_compl] using core.isClosed.isOpen_compl
  obtain ⟨d,ds,dt,de⟩ := open_coordinate_of_subsets os (exteriorPlaneBase_isOpen R) (nonT.map E.symm) E
  let P := helicoidConformalBaseHomeomorph
  let e := d.trans P.symm.toOpenPartialHomeomorph
  have es : e.source=S := by ext x; change x∈d.source ∧ d x∈Set.univ ↔ _; simp [ds]
  have et : e.target=P ⁻¹' T := by ext z; change z∈Set.univ ∧ P z∈d.target ↔ _; simp [dt,T]
  let U := extendOpenScalar u
  have coordValue (x : S) : P (e x.1)=(E x).1 := by
    change P (P.symm (d x.1))=_
    rw [P.apply_symm_apply,de]
  have actual (x : S) : |U (P (e x.1))|≤1/2 ∧ Y x.1=helicoidGraphMap U (P (e x.1)) := by
    rw [coordValue]
    have eq : U (E x).1=u (E x) := by simp only [U,extendOpenScalar,dite_eq_left (E x).2]
    refine ⟨by simpa only [eq] using bound (E x),?_⟩
    change Y x.1=helicoidTubeMap ((U (E x).1,(E x).1.1),(E x).1.2)
    rw [eq]
    exact formula x
  have tail : e.source∈cocompact M := by rw [es]; simpa only [compl_compl] using core.compl_mem_cocompact
  have escape : Tendsto (fun x => ‖Y x‖) (cocompact M) atTop :=
    tendsto_norm_cocompact_atTop.comp (isProperMap_iff_tendsto_cocompact.mp (coordinateToTube_isProperMap proper)).2
  have limit := bounded_helicoid_graph_escape (Z:=fun x => e x) (s:=fun x => U (P (e x))) (Y:=Y)
    (show ∀ᶠ x in cocompact M, |U (P (e x))|≤1 ∧
      Y x=helicoidTubeMap ((U (P (e x)),Real.sinh (e x).re),(e x).im) from
      by
        filter_upwards [tail] with x hx
        exact ⟨(actual ⟨x,es ▸ hx⟩).1.trans (by norm_num),(actual ⟨x,es ▸ hx⟩).2⟩) escape
  have far : e.target∈cobounded ℂ := by
    rw [et]
    exact (tendsto_norm_cobounded_atTop.comp helicoidConformalBase_proper).eventually_gt_atTop R
  refine ⟨e,U,tail,far,limit,?_⟩
  intro z hz
  have base : z∈P ⁻¹' T := et ▸ hz
  have q := actual ⟨e.symm z,es ▸ e.map_target hz⟩
  simp only [e.right_inv hz] at q
  refine ⟨smooth.contDiffAt ((exteriorPlaneBase_isOpen R).mem_nhds base),q.1,?_⟩
  exact (tubeCartesian_coordinateToTube (X (e.symm z))).symm.trans (congrArg tubeCartesian q.2)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidHeightEnd.physical_parameter
