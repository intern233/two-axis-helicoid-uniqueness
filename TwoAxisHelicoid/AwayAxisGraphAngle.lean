import TwoAxisHelicoid.HelicoidTubeAngularEstimate

namespace TwoAxisHelicoid
open Set Filter Bornology Complex
open scoped Topology ComplexConjugate

/-- Away from the reference axis, a helicoidal graph with decaying
normal displacement has asymptotically real horizontal direction in
the rotating frame. The surface need not contain the axis. -/
theorem HasHelicoidC1End.angular_bound_away_from_axis {M : Type*} [TopologicalSpace M]
    {Y : M → HelicoidTubeCoordinates} (graphEnd : HasHelicoidC1End Y) (cy : Continuous Y)
    {ε : ℝ} (ep : 0<ε) :
    ∃ B : ℝ, ∀ x : M, B≤‖Y x‖ → 1≤‖tubeRelativeHorizontal (Y x)‖ →
      |(tubeRelativeHorizontal (Y x)).im|≤ε*‖tubeRelativeHorizontal (Y x)‖ := by
  obtain ⟨C,_,R,_,compact,E,_,u,_,graph,decay⟩ := graphEnd
  obtain ⟨T,_,hT⟩ := ((hasBasis_cobounded_norm.comap
    (Subtype.val : exteriorPlaneBase R → ℝ × ℝ)).eventually_iff).mp (decay.eventually (gt_mem_nhds (half_pos ep)))
  obtain ⟨B,bound⟩ := (compact.image cy).isBounded.exists_norm_le
  refine ⟨max B T+2,fun x hx away => ?_⟩
  have hx' : x ∈ helicoidProjectedEnd Y C (exteriorPlaneBase R) := by
    by_contra h
    linarith [bound _ (mem_image_of_mem Y h),le_max_left B T]
  let p := E ⟨x,hx'⟩
  have pos : Y x=helicoidTubeMap ((u p,p.1.1),p.1.2) := by simpa only [p,E.symm_apply_apply] using (graph p).2
  have cert := helicoid_normal_graph_angular_estimate p.1.1 p.1.2 (u p)
  rw [← pos] at cert
  have hp : T≤‖p.1‖ := by linarith [le_max_right B T,cert.2.2,(graph p).1]
  have small : |u p|≤ε/2 := (lt_of_le_of_lt (le_add_of_nonneg_right (Real.sqrt_nonneg _))
    (hT (show p∈(Subtype.val : exteriorPlaneBase R → ℝ × ℝ) ⁻¹' {z | T≤‖z‖} from hp))).le
  exact cert.1.trans (by nlinarith [mul_le_mul cert.2.1 small (abs_nonneg _) (norm_nonneg _),
    mul_le_mul_of_nonneg_left away (half_pos ep).le])

/-- The quotient by its conjugate records an unoriented horizontal
line, so this limit handles both signs of the horizontal radius. -/
theorem HasHelicoidC1End.relative_phase_on_escaping_ray {M : Type*} [TopologicalSpace M]
    {Y : M → HelicoidTubeCoordinates} (graph : HasHelicoidC1End Y) (cy : Continuous Y)
    {p : ℝ → M} (spatial : Tendsto (fun t => ‖Y (p t)‖) atTop atTop)
    (horizontal : Tendsto (fun t => ‖tubeRelativeHorizontal (Y (p t))‖) atTop atTop) :
    let z := fun t => tubeRelativeHorizontal (Y (p t))
    Tendsto (fun t => z t / conj (z t)) atTop (𝓝 1) := by
  let z := fun t => tubeRelativeHorizontal (Y (p t))
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  obtain ⟨B,bound⟩ := graph.angular_bound_away_from_axis cy (show 0<ε/4 by positivity)
  filter_upwards [spatial.eventually_ge_atTop B,horizontal.eventually_ge_atTop 1] with t ht h
  have pos : 0<‖z t‖ := zero_lt_one.trans_le h
  have ne : conj (z t)≠0 := (map_ne_zero _).mpr (norm_pos_iff.mp pos)
  have diff : z t-conj (z t)=((2*(z t).im:ℝ):ℂ)*I := by apply Complex.ext <;> simp; ring
  change dist (z t/conj (z t)) 1<ε
  rw [dist_eq_norm,div_sub_one ne,diff,norm_div,norm_conj,norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact (div_lt_iff₀ pos).mpr (by nlinarith [bound (p t) ht h,mul_pos ep pos])

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.angular_bound_away_from_axis
#print axioms TwoAxisHelicoid.HasHelicoidC1End.relative_phase_on_escaping_ray
