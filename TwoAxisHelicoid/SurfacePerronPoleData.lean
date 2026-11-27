import TwoAxisHelicoid.MarkedDiskPolePatch
import TwoAxisHelicoid.LocalLogarithmicInsertion
import TwoAxisHelicoid.PerronGreenPotential

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

/-- Compatible Perron functions with a common logarithmic pole and
a compact core outside which the upper function vanishes. -/
structure SurfacePerronPoleData (N : Type*) [TopologicalSpace N] [T2Space N] [ChartedSpace ℂ N] where
  p : N
  L : openSurfacePuncture p → ℝ
  H : openSurfacePuncture p → ℝ
  subharmonic : ∀ x, SurfaceSubharmonicAt L x
  superharmonic : ∀ x, SurfaceSubharmonicAt (fun y => -H y) x
  order : L≤H
  nonpositive : ∀ x, H x≤0
  negative : ∃ x, H x<0
  pole_bound : ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] (chartAt ℂ p p), let x := (chartAt ℂ p).symm z
    Real.log ‖z-chartAt ℂ p p‖-C≤openSetExtension (openSurfacePuncture p) L x ∧
    openSetExtension (openSurfacePuncture p) H x≤Real.log ‖z-chartAt ℂ p p‖+C
  core : Set N
  compact : IsCompact core
  pole_mem : p∈core
  exterior : ∃ D : ℝ, ∀ x : openSurfacePuncture p, x.val∉core → -D≤L x ∧ H x=0

/-- Construct both functions on the actual punctured surface. The
logarithmic coefficient is one in the distinguished chart at the pole,
even when the quadratic patch is in a different maximal-atlas chart. -/
theorem perron_pole_data_of_quadratic_patch {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ,ℂ) ω N] (s : QuadraticSurfacePolePatch N) : Nonempty (SurfacePerronPoleData N) := by
  classical
  let e := s.chart
  let c := e s.p
  let r := s.r
  have rp : 0<r := s.positive
  let V := openSurfacePuncture s.p
  obtain ⟨δ,cδ,nδ,inδ,loδ,zero⟩ := continuous_capped_chart_radius e c (by positivity : 0<2*r) s.domain
  let d := fun x : V => δ x.val/r
  have dc : Continuous d := (cδ.comp continuous_subtype_val).div_const r
  have dp (x : V) : 0<d x := div_pos (lt_of_le_of_ne (nδ _) (fun eq =>
    x.2 (((zero _).mp eq.symm).trans (e.left_inv s.in_source)))) rp
  have small (x : V) (h : d x<2) : x.val∈e.source ∧ δ x.val=‖e x.val-c‖ :=
    loδ x.val ((div_lt_iff₀ rp).mp h)
  obtain ⟨L,H,K,sl,sh,order,bd,outer,inner⟩ := insert_pole_into_quadratic_patch d dc dp (fun x : V => s.B x.val)
    (fun x => surface_subharmonic_open_subtype V x (s.subharmonic x.val)) (fun x => s.bounded x.val)
    (fun x : V => e x.val) c s.weight rp
    (fun x hx => (contMDiffAt_of_mem_maximalAtlas s.maximal (small x hx).1).comp x contMDiff_subtype_val.contMDiffAt)
    (fun x hx => by
      obtain ⟨src,rad⟩ := small x hx
      have right := s.quadratic x.val src (rad ▸ (div_lt_iff₀ rp).mp hx)
      refine ⟨?_,right⟩
      change ‖e x.val-c‖=r*(δ x.val/r)
      rw [← rad]; field_simp)
  let C := e.symm '' closedBall c r
  have srcball : closedBall c r⊆e.target := (closedBall_subset_closedBall (by linarith : r≤2*r)).trans s.domain
  have ck : IsCompact C := (isCompact_closedBall _ _).image_of_continuousOn (e.symm.continuousOn.mono srcball)
  have cp : s.p∈C := ⟨c,mem_closedBall_self rp.le,e.left_inv s.in_source⟩
  have ext (x : V) (outside : x.val∉C) : 1≤d x := by
    apply le_of_not_gt
    intro h
    obtain ⟨xs,eq⟩ := small x (h.trans (by norm_num))
    have size := (div_lt_iff₀ rp).mp h
    rw [one_mul,eq] at size
    exact outside ⟨e x.val,mem_closedBall.mpr (by simpa only [dist_eq_norm] using size.le),e.left_inv xs⟩
  let a := chartAt ℂ s.p
  let z₀ := a s.p
  have ps : s.p∈a.source := mem_chart_source ℂ s.p
  have back : Tendsto a.symm (𝓝 z₀) (𝓝 s.p) := by simpa only [a.left_inv ps,z₀] using (a.symm.continuousAt (a.map_source ps)).tendsto
  have δp : δ s.p=0 := (zero _).mpr (e.left_inv s.in_source).symm
  have near : ∀ᶠ z in 𝓝 z₀, δ (a.symm z)<r := ((cδ.tendsto s.p).comp back).eventually (gt_mem_nhds (show δ s.p<r by rwa [δp]))
  have punct : ∀ᶠ z in 𝓝[≠] z₀, ∃ x : V, x.val=a.symm z ∧ d x<1 ∧ δ x.val=‖e x.val-c‖ := by
    filter_upwards [near.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (a.open_target.mem_nhds (a.map_source ps))] with z sz ne ht
    have nz : a.symm z≠s.p := fun eq => ne ((a.right_inv ht).symm.trans (congrArg a eq))
    let x : V := ⟨a.symm z,nz⟩
    have h : d x<1 := (div_lt_iff₀ rp).mpr (by simpa only [one_mul] using sz)
    exact ⟨x,rfl,h,(small x (h.trans (by norm_num))).2⟩
  obtain ⟨z,⟨w,_,dw,_⟩⟩ := punct.exists
  have negative : H w<0 := (inner w dw).2.trans_lt (Real.log_neg (dp w) dw)
  refine ⟨⟨s.p,L,H,sl,sh,order,fun x => (bd x).2,⟨w,negative⟩,?_,C,ck,cp,K,fun x hx => outer x (ext x hx)⟩⟩
  obtain ⟨b,limit⟩ := logarithmic_chart_radius_difference s.maximal s.in_source
  refine ⟨|b|+|Real.log r|+|K|+2,?_⟩
  filter_upwards [punct,limit.eventually (Ioo_mem_nhds (show b-1<b by linarith) (show b<b+1 by linarith))] with z info close
  obtain ⟨x,hx,dx,radius⟩ := info
  have l : openSetExtension V L (a.symm z)=L x := hx ▸ openSetExtension_val V L x
  have h : openSetExtension V H (a.symm z)=H x := hx ▸ openSetExtension_val V H x
  change Real.log ‖z-z₀‖-(|b|+|Real.log r|+|K|+2)≤openSetExtension V L (a.symm z) ∧
    openSetExtension V H (a.symm z)≤Real.log ‖z-z₀‖+(|b|+|Real.log r|+|K|+2)
  rw [l,h]
  have dlog : Real.log (d x)=Real.log ‖e (a.symm z)-c‖-Real.log r := by
    have ne : δ x.val≠0 := fun eq => (dp x).ne' (by change δ x.val/r=0; rw [eq,zero_div])
    rw [show d x=δ x.val/r from rfl,Real.log_div ne rp.ne',radius,hx]
  obtain ⟨lo,up⟩ := inner x dx
  rw [dlog] at lo up
  change b-1<Real.log ‖e (a.symm z)-c‖-Real.log ‖z-z₀‖ ∧ Real.log ‖e (a.symm z)-c‖-Real.log ‖z-z₀‖<b+1 at close
  constructor <;> linarith [close.1,close.2,le_abs_self b,neg_abs_le b,le_abs_self (Real.log r),neg_abs_le (Real.log r),le_abs_self K,abs_nonneg K]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.perron_pole_data_of_quadratic_patch
