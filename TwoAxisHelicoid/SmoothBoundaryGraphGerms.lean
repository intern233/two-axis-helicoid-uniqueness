import TwoAxisHelicoid.SmoothRegionChartPartition
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace TwoAxisHelicoid
open Complex Metric Filter Set Topology Function
open scoped Topology ContDiff Manifold

/-- The usual local graph condition at each boundary point. The defining
function and the description of the interior are needed only as germs. -/
def HasSmoothBoundaryGraphGerms {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] (Ω : Set M) : Prop :=
  ∀ p∈frontier Ω, ∃ e : OpenPartialHomeomorph M ℂ, e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧ p∈e.source ∧
    ∃ φ : ℝ → ℝ, ContDiffAt ℝ 2 φ (e p).re ∧ (e p).im=φ (e p).re ∧
      ∀ᶠ z in 𝓝 (e p), z∈curveChartRegion e Ω ↔ φ z.re<z.im

private theorem global_c2_from_germ {f : ℝ → ℝ} {a : ℝ} (smooth : ContDiffAt ℝ 2 f a) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨r,rp,ballSub⟩ := Metric.mem_nhds_iff.mp (smooth.eventually (by norm_num))
  let b : ContDiffBump a := ⟨r/4,r/2,by positivity,by linarith⟩
  refine ⟨fun x => b x*f x,contDiff_iff_contDiffAt.mpr ?_,?_⟩
  · intro x
    by_cases h : dist x a<r
    · exact b.contDiff.contDiffAt.mul (ballSub h)
    · have gap : r/2<dist x a := by linarith [le_of_not_gt h]
      have near := ((continuous_id.dist continuous_const).continuousAt (x:=x)).tendsto.eventually (Ioi_mem_nhds gap)
      apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      filter_upwards [near] with y hy
      rw [b.zero_of_le_dist (show b.rOut≤dist y a from hy.le),zero_mul]
  · filter_upwards [b.eventuallyEq_one] with x hx
    rw [show b x=1 from hx,one_mul]

/-- A defining graph in a neighborhood of each physical boundary point
produces the rectangular charts needed for integration and a finite
partition. All extensions and chart sizes are constructed internally. -/
theorem smooth_curve_boundary_of_graph_germs {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {Ω : Set M} (germs : HasSmoothBoundaryGraphGerms Ω) : HasSmoothCurveBoundary Ω := by
  intro p hp
  obtain ⟨e,atlas,src,f,smooth,center,localSide⟩ := germs p hp
  obtain ⟨φ,cφ,same⟩ := global_c2_from_germ smooth
  let a := (e p).re
  let c : ℝ×ℝ := (a,0)
  let T := Complex.equivRealProdCLM.symm ∘ realGraphShear φ
  let J := fun z : ℂ => (z.re,z.im-φ z.re)
  have jt : Continuous J := continuous_re.prodMk (continuous_im.sub (cφ.continuous.comp continuous_re))
  have ct : Continuous T := Complex.equivRealProdCLM.symm.continuous.comp
    (continuous_fst.prodMk (continuous_snd.add (cφ.continuous.comp continuous_fst)))
  have base : φ a=(e p).im := same.self_of_nhds.trans center.symm
  have tc : T c=e p := by apply Complex.ext <;> simp [T,c,realGraphShear,a,Complex.equivRealProdCLM_symm_apply,← base]
  have jc : J (e p)=c := Prod.ext rfl (by change (e p).im-φ a=0; rw [base,sub_self])
  have inverse (z : ℂ) : T (J z)=z := by
    apply Complex.ext <;> simp [T,J,realGraphShear,Complex.equivRealProdCLM_symm_apply]
  have near : ∀ᶠ q in 𝓝 c, T q∈e.target ∧ (T q∈curveChartRegion e Ω ↔ 0<q.2) := by
    have tend : Tendsto T (𝓝 c) (𝓝 (e p)) := tc ▸ ct.continuousAt
    have agree : ∀ᶠ q : ℝ×ℝ in 𝓝 c, φ q.1=f q.1 := same.comp_tendsto continuous_fst.continuousAt
    filter_upwards [tend.eventually (e.open_target.mem_nhds (e.map_source src)),tend.eventually localSide,agree] with q ht hs eq
    refine ⟨ht,hs.trans ?_⟩
    change f q.1<q.2+φ q.1 ↔ 0<q.2
    rw [← eq]
    constructor <;> intro h <;> linarith
  obtain ⟨r,rp,small⟩ := Metric.mem_nhds_iff.mp near
  let s := r/2
  have sp : 0<s := half_pos rp
  have box (q : ℝ×ℝ) (hq : q∈Icc (a-s,-s) (a+s,s)) : q∈ball c r := by
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff,Real.dist_eq,Real.dist_eq]
    change |q.1-a|<r ∧ |q.2-0|<r
    have sx := hq.1.1
    have sy := hq.1.2
    have tx := hq.2.1
    have ty := hq.2.2
    dsimp only at sx sy tx ty
    constructor <;> apply abs_lt.mpr <;> constructor <;> dsimp only [s] at * <;> linarith
  let G : CurveBoundaryGraph e Ω :=
    {φ:=φ,smooth:=cφ,l:=a-s,r:=a+s,d:=s,ordered:=by linarith,depth:=sp,
     side:=fun q hq => (small (box q hq)).2,
     boundary:=fun x hx => by
       have hq : (x,(0:ℝ))∈Icc (a-s,-s) (a+s,s) := ⟨⟨hx.1,neg_nonpos.mpr sp.le⟩,hx.2,sp.le⟩
       simpa only [T,Function.comp_apply,realGraphShear,zero_add] using (small (box _ hq)).1}
  refine ⟨e,atlas,G,?_⟩
  have centerMem : c∈Ioo (a-s) (a+s) ×ˢ Ioo (-s) s := by
    exact ⟨⟨by dsimp [c]; linarith,by dsimp [c]; linarith⟩,neg_lt_zero.mpr sp,sp⟩
  have nearJ : Tendsto (J ∘ e) (𝓝 p) (𝓝 c) := jc ▸ jt.continuousAt.comp (e.continuousAt src)
  filter_upwards [e.open_source.mem_nhds src,
    nearJ.eventually ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds centerMem)] with x hx inner
  exact ⟨hx,⟨J (e x),inner,inverse _⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_curve_boundary_of_graph_germs

