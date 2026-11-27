import TwoAxisHelicoid.OpenSubsetCoordinate
import TwoAxisHelicoid.HelicoidGraphExteriorMetric
import TwoAxisHelicoid.ExteriorComplexEnd
import TwoAxisHelicoid.UniformExteriorDoublePoints

namespace TwoAxisHelicoid
open Complex Real Set Filter Metric Bornology Topology
open scoped Topology

/-- Reciprocal natural helicoid coordinates give a genuine topological
chart on the one-point compactification of the physical surface.
In these coordinates the actual spatial height differs from the
imaginary part of the exterior parameter by at most one. -/
theorem HasHelicoidC1End.natural_puncture_coordinate {M : Type*} [TopologicalSpace M]
    [T2Space M] [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    {X : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End X) (proper : IsProperMap X) :
    ∃ D : PuncturedComplexEnd M, ∀ᶠ x in cocompact M,
      D.coord x=(helicoidProjectedComplexParameter (X x))⁻¹ ∧
      |(X x).2-(helicoidProjectedComplexParameter (X x)).im|≤1 := by
  classical
  obtain ⟨C,_,R,hR,core,E,proj,u,_,spatial,_⟩ := graph
  let S := helicoidProjectedEnd X C (exteriorPlaneBase R)
  let T := exteriorPlaneBase R
  have nonT : Nonempty T := ⟨⟨(0,R+1),by
    change R<‖((0:ℝ),R+1)‖
    have bd := norm_snd_le ((0:ℝ),R+1)
    change ‖R+1‖≤‖((0:ℝ),R+1)‖ at bd
    rw [Real.norm_eq_abs,abs_of_pos (by linarith : 0<R+1)] at bd
    exact (lt_add_one R).trans_le bd⟩⟩
  have nonS : Nonempty S := nonT.map E.symm
  have os : IsOpen S := by simpa only [compl_compl] using core.isClosed.isOpen_compl
  obtain ⟨d,ds,dt,de⟩ := open_coordinate_of_subsets os (exteriorPlaneBase_isOpen R) nonS E
  let P := helicoidConformalBaseHomeomorph
  let e := d.trans P.symm.toOpenPartialHomeomorph
  have es : e.source=S := by ext x; change x∈d.source ∧ d x∈Set.univ ↔ _; simp [ds]
  have et : e.target=P ⁻¹' T := by ext z; change z∈Set.univ ∧ P z∈d.target ↔ _; simp [dt,T]
  let F := fun x => helicoidProjectedComplexParameter (X x)
  have pr (x : S) : (E x).1=helicoidBaseCoordinates (X x.1) := congrArg Subtype.val (congrFun proj x)
  have ef (x : S) : e x.1=F x.1 := by
    change P.symm (d x.1)=P.symm (helicoidBaseCoordinates (X x.1))
    rw [de,pr]
  have recover (x : S) : P (e x.1)=(E x).1 := by change P (P.symm (d x.1))=_; rw [P.apply_symm_apply,de]
  have tail : S∈cocompact M := by simpa only [compl_compl] using core.compl_mem_cocompact
  let shift := fun x : M => if hx : x∈S then u (E ⟨x,hx⟩) else 0
  have actual (x : M) (hx : x∈S) : |shift x|≤1/2 ∧ X x=helicoidTubeMap ((shift x,Real.sinh (e x).re),(e x).im) := by
    let p : S := ⟨x,hx⟩
    have g := spatial (E p)
    have val : (E.symm (E p)).1=x := congrArg Subtype.val (E.symm_apply_apply p)
    rw [val] at g
    have b := recover p
    change (Real.sinh (e x).re,(e x).im)=(E p).1 at b
    have a := congrArg (fun q : ℝ × ℝ => q.1) b
    have h := congrArg (fun q : ℝ × ℝ => q.2) b
    change Real.sinh (e x).re=(E p).1.1 at a
    change (e x).im=(E p).1.2 at h
    rw [a,h]
    exact (by simpa only [shift,dite_eq_left hx] using g)
  have tailEv : ∀ᶠ x in cocompact M, x∈S := tail
  have esc : Tendsto (fun x => ‖e x‖) (cocompact M) atTop :=
    bounded_helicoid_graph_escape (Z := e) (s := shift) (Y := X)
      (tailEv.mono fun x hx => ⟨(actual x hx).1.trans (by norm_num),(actual x hx).2⟩)
      (tendsto_norm_cocompact_atTop.comp (isProperMap_iff_tendsto_cocompact.mp proper).2)
  have all : e.target ∈ cobounded ℂ := by
    rw [et]
    exact (tendsto_norm_cobounded_atTop.comp helicoidConformalBase_proper).eventually (eventually_gt_atTop R)
  obtain ⟨A,_,far⟩ := hasBasis_cobounded_norm.eventually_iff.mp all
  let B := max A 1+1
  have pb : 0<B := by dsimp [B]; linarith [le_max_right A 1]
  let V := {z : ℂ | B<‖z‖}
  let f := e.trans (OpenPartialHomeomorph.ofSet V (isOpen_lt continuous_const continuous_norm))
  have ft : f.target=V := by
    ext z
    change z∈V ∧ z∈e.target ↔ z∈V
    refine ⟨And.left,fun hz => ⟨hz,far ?_⟩⟩
    change A≤‖z‖
    change max A 1+1<‖z‖ at hz
    linarith [le_max_left A 1]
  have fc : IsCompact f.sourceᶜ := isCompact_exteriorChartCore e (es ▸ core) esc B
  let D := exteriorCoordinateComplexEnd f pb ft fc esc
  refine ⟨D,?_⟩
  filter_upwards [tail] with x hx
  have eq := ef ⟨x,hx⟩
  change (e x)⁻¹=(F x)⁻¹ ∧ |(X x).2-(F x).im|≤1
  rw [← eq]
  refine ⟨rfl,?_⟩
  have h := congrArg Prod.snd (actual x hx).2
  change (X x).2=(e x).im+helicoidAngle (Real.sinh (e x).re) (shift x) at h
  rw [h,add_sub_cancel_left]
  exact helicoidAngle_abs_le ((actual x hx).1.trans (by norm_num))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.natural_puncture_coordinate
