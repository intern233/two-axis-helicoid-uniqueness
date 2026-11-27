import TwoAxisHelicoid.RegularPlaneZeroGraph
namespace TwoAxisHelicoid
open Function Metric Set Topology Filter
open scoped Topology ContDiff

/-- The zero set of a C² defining function with positive vertical
derivative is genuinely the graph of a C² function, including the
identification of its positive side. -/
theorem regular_defining_function_upper_graph {F : ℝ×ℝ → ℝ} {p : ℝ×ℝ} (smooth : ContDiffAt ℝ 2 F p)
    (zero : F p=0) (positive : 0<fderiv ℝ F p (0,1)) :
    ∃ φ : ℝ → ℝ, ContDiffAt ℝ 2 φ p.1 ∧ φ p.1=p.2 ∧
      ∀ᶠ q in 𝓝 p, 0<F q ↔ φ q.1<q.2 := by
  obtain ⟨φ,sp,atp,zf,_⟩ := regular_plane_zero_graph (by norm_num) smooth zero positive.ne'
  have cder : ContinuousAt (fun q => fderiv ℝ F q (0,1)) p :=
    (smooth.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have good : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 F q ∧ 0<fderiv ℝ F q (0,1) :=
    (smooth.eventually (by norm_num)).and (cder.eventually (Ioi_mem_nhds positive))
  obtain ⟨U,hU,V,hV,inside⟩ := mem_nhds_prod_iff.mp good
  obtain ⟨r,rp,ballV⟩ := Metric.mem_nhds_iff.mp hV
  let B := ball p.2 r
  have mono (x : ℝ) (hx : x∈U) : StrictMonoOn (fun y => F (x,y)) B := by
    have d (y : ℝ) (hy : y∈B) : HasDerivAt (fun t => F (x,t)) (fderiv ℝ F (x,y) (0,1)) y :=
      (((inside ⟨hx,ballV hy⟩).1.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt y
        ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
    apply strictMonoOn_of_deriv_pos (convex_ball _ _)
    · exact fun y hy => (d y hy).continuousAt.continuousWithinAt
    · intro y hy
      have mem := interior_subset hy
      rw [(d y mem).deriv]
      exact (inside ⟨hx,ballV mem⟩).2
  have yφ : Tendsto (fun q : ℝ×ℝ => φ q.1) (𝓝 p) (𝓝 p.2) :=
    atp ▸ sp.continuousAt.comp continuous_fst.continuousAt
  have near := ball_mem_nhds p.2 rp
  refine ⟨φ,sp,atp,?_⟩
  filter_upwards [continuous_fst.continuousAt.eventually hU,
    continuous_snd.continuousAt.eventually near,yφ.eventually near,
    (continuous_fst.continuousAt (x:=p)).eventually zf] with q x y curve vanishes
  have eq := (mono q.1 x).lt_iff_lt curve y
  change F (q.1,φ q.1)<F q ↔ φ q.1<q.2 at eq
  rw [show F (q.1,φ q.1)=0 from vanishes] at eq
  exact eq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_defining_function_upper_graph

