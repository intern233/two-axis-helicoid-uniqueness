import TwoAxisHelicoid.MarkedLogGaussGrowth
import TwoAxisHelicoid.HelicoidAxisRadialTangent
import TwoAxisHelicoid.AxisLiftBound
import TwoAxisHelicoid.MeromorphicRayOrder

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology
open scoped Topology ComplexConjugate

/-- Along the marked puncture the true Gauss direction avoids the
outward horizontal radial direction of the projected normal graph. -/
theorem marked_helicoid_radial_avoidance {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (proper : IsProperMap (harmonicTorusImmersion hX))
    (graph : HasHelicoidC1End (coordinateToTube ∘ harmonicTorusImmersion hX)) :
    let p := puncturedImmersionCoefficient (rhombicPeriodPair t ht) X
    let Q := helicoidProjectedComplexParameter ∘ (coordinateToTube ∘ X)
    ∀ᶠ z in 𝓝[≠] (0:ℂ), nullGauss (p z)≠Complex.exp (((Q z).im:ℂ)*I) := by
  let L := rhombicPeriodPair t ht
  let p := puncturedImmersionCoefficient L X
  let P := helicoidProjectedComplexParameter ∘ (coordinateToTube ∘ X)
  obtain ⟨E,chart,_,_⟩ := hX.standard_end_chart
  obtain ⟨u,geo⟩ := graph.eventually_natural_graph (coordinateToTube_isProperMap proper)
  let G := helicoidGraphMap u ∘ helicoidConformalBase
  have ev : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ u (helicoidConformalBase (P z)) ∧
      coordinateToTube (X z)=G (P z) ∧ coordinateToTube (X z)∈helicoidTubeEquiv.target := by
    filter_upwards [E.from_zero.eventually geo,chart] with z h c
    let Y := coordinateToTube ∘ harmonicTorusImmersion hX
    let a := E.coord.symm z
    change Y a=coordinateToTube (X z) at c
    change 2<‖helicoidProjectedComplexParameter (Y a)‖ ∧ _ at h
    obtain ⟨_,d,_,eq,tube⟩ := h
    change DifferentiableAt ℝ u (helicoidConformalBase (helicoidProjectedComplexParameter (Y a))) at d
    change Y a=G (helicoidProjectedComplexParameter (Y a)) at eq
    change Y a∈helicoidTubeEquiv.target at tube
    rw [c] at d eq tube
    exact ⟨d,eq,tube⟩
  have geq : coordinateToTube ∘ X =ᶠ[𝓝[≠] (0:ℂ)] G ∘ P := ev.mono fun _ h => h.2.1
  obtain ⟨_,ord⟩ := marked_helicoid_height_double_pole ht hX proper graph
  have neg : meromorphicOrderAt (fun z => p z 2) 0<0 := by rw [ord]; exact_mod_cast (by decide : (-2:ℤ)<0)
  have big := (tendsto_norm_cobounded_atTop.comp (tendsto_cobounded_of_meromorphicOrderAt_neg neg)).eventually_gt_atTop 0
  have hp := hX.null_differential (fun _ hz => rhombic_conj_mem ht hz)
  filter_upwards [ev,punctured_germ_eventually_local geq,punctured_lattice_regular_near_zero L,big] with z h localEq reg nz
  exact graph_gauss_ne_radial (puncturedImmersionCoefficient_hasFDerivAt hX reg) (hp.null z reg)
    (norm_pos_iff.mp nz) (hX.immersion z reg) h.2.2 h.1 localEq

theorem marked_helicoid_height_radius_bound {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (proper : IsProperMap (harmonicTorusImmersion hX))
    (graph : HasHelicoidC1End (coordinateToTube ∘ harmonicTorusImmersion hX)) :
    ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖z‖*|X z 2|≤B := by
  let L := rhombicPeriodPair t ht
  let := punctured_complex_curve_noncompact (0:PeriodTorus L)
  let : LocallyCompactSpace (PuncturedPeriodTorus L) := ChartedSpace.locallyCompactSpace ℂ _
  obtain ⟨E,eq,sm,iso⟩ := hX.standard_end_chart
  obtain ⟨H,d⟩ := hX.complex_coordinate_primitive ht 2
  have ev := (punctured_lattice_regular_near_zero L).mono d
  have height : ∀ᶠ z in 𝓝[≠] (0:ℂ), ((coordinateToTube ∘ harmonicTorusImmersion hX) (E.coord.symm z)).2=(H z).re+0 := by
    filter_upwards [eq,ev] with z c h
    exact (congrArg Prod.snd c).trans (by change X z 2=(H z).re+0; rw [h.2,add_zero])
  obtain ⟨mer,order,_,_⟩ := graph.intrinsic_height_orders (coordinateToTube_isProperMap proper) E sm iso height
    (ev.mono fun _ h => h.1.differentiableAt)
  obtain ⟨C,bd⟩ := simple_pole_norm_times_radius_bounded mer order
  refine ⟨C,?_⟩
  filter_upwards [ev,bd] with z h b
  rw [← h.2]
  exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)).trans b

theorem null_gauss_unit_on_imaginary_axis {L : PeriodPair} {p : ℂ → Fin 3 → ℂ}
    (hp : TwoAxisNullDifferential L p) {z : ℂ} (reg : z∉L.lattice) (nh : p z 2≠0) (axis : z.re=0) :
    ‖nullGauss (p z)‖=1 := by
  have cj : conj z= -z := by apply Complex.ext <;> simp [axis]
  have c := null_gauss_conjugation hp reg
  rw [cj] at c
  have n := congrArg norm (null_gauss_neg_product hp reg nh)
  rw [c,norm_mul,norm_neg,Complex.norm_conj,norm_neg,norm_one] at n
  nlinarith [norm_nonneg (nullGauss (p z))]

private theorem purely_imaginary_eq {z : ℂ} (h : z.re=0) : z=(z.im:ℂ)*I := by
  apply Complex.ext <;> simp [h,Complex.mul_re,Complex.mul_im]

/-- On the actual positive imaginary parameter ray the lifted Gauss
angle differs from the physical height by a bounded amount. -/
theorem marked_helicoid_axis_phase_bound {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (proper : IsProperMap (harmonicTorusImmersion hX))
    (graph : HasHelicoidC1End (coordinateToTube ∘ harmonicTorusImmersion hX))
    {F : ℂ → ℂ} (logF : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z ∧
      Complex.exp (F z)=nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) :
    let j := fun y : ℝ => (y:ℂ)*I
    ∃ B : ℝ, 0≤B ∧ ∀ᶠ y in 𝓝[>] (0:ℝ), ‖F (j y)‖=|(F (j y)).im| ∧
      |(F (j y)).im-X (j y) 2|≤B := by
  let L := rhombicPeriodPair t ht
  let p := puncturedImmersionCoefficient L X
  let j := fun y : ℝ => (y:ℂ)*I
  let β := fun y => (F (j y)).im-X (j y) 2
  have cj : Continuous j := Complex.continuous_ofReal.mul continuous_const
  have hp := hX.null_differential (fun _ hz => rhombic_conj_mem ht hz)
  obtain ⟨_,ord⟩ := marked_helicoid_height_double_pole ht hX proper graph
  have neg : meromorphicOrderAt (fun z => p z 2) 0<0 := by rw [ord]; exact_mod_cast (by decide : (-2:ℤ)<0)
  have big := (tendsto_norm_cobounded_atTop.comp (tendsto_cobounded_of_meromorphicOrderAt_neg neg)).eventually_gt_atTop 0
  have ev : ∀ᶠ y in 𝓝[>] (0:ℝ), ContinuousAt β y ∧ Complex.exp ((β y:ℂ)*I)≠1 ∧ ‖F (j y)‖=|(F (j y)).im| := by
    filter_upwards [positive_imaginary_ray_tendsto.eventually logF,positive_imaginary_ray_tendsto.eventually big,
      positive_imaginary_ray_tendsto.eventually (punctured_lattice_regular_near_zero L),
      positive_imaginary_ray_tendsto.eventually (marked_helicoid_radial_avoidance ht hX proper graph)] with y f b reg avoid
    have axis : (j y).re=0 := by simp [j,Complex.mul_re]
    have unit := null_gauss_unit_on_imaginary_axis hp reg (norm_pos_iff.mp b) axis
    rw [← f.2,Complex.norm_exp,Real.exp_eq_one_iff] at unit
    have pure := purely_imaginary_eq unit
    have norm : ‖F (j y)‖=|(F (j y)).im| := by
      conv_lhs => rw [pure]
      rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    have vert := hX.vertical_axis_zero reg axis
    have tube : coordinateToTube (X (j y))=((0,0),X (j y) 2) := by
      change ((X (j y) 0,X (j y) 1),X (j y) 2)=_
      rw [vert.1,vert.2]
    have phase := helicoid_projected_parameter_axis (X (j y) 2)
    change nullGauss (p (j y))≠Complex.exp (((helicoidProjectedComplexParameter (coordinateToTube (X (j y)))).im:ℂ)*I) at avoid
    rw [tube,phase] at avoid
    have cf : ContinuousAt (F ∘ j) y := (show ContinuousAt F (j y) from f.1.continuousAt).comp (f := j) cj.continuousAt
    have cx : ContinuousAt (X ∘ j) y := (show ContinuousAt X (j y) from (hX.differentiable _ reg).continuousAt).comp (f := j) cj.continuousAt
    refine ⟨(continuous_im.continuousAt.comp cf).sub ((continuous_apply (2:Fin 3)).continuousAt.comp cx),?_,norm⟩
    intro bad
    apply avoid
    rw [← f.2]
    have de : F (j y)=(β y:ℂ)*I+(X (j y) 2:ℂ)*I := by
      rw [pure]; dsimp [β]; push_cast; ring
    rw [de,Complex.exp_add,bad,one_mul]
  obtain ⟨r,hr,sub⟩ := Metric.mem_nhdsWithin_iff.mp ev
  have e (y : ℝ) (hy : y∈Ioo 0 r) := sub (show y∈ball (0:ℝ) r ∩ Ioi 0 from
    ⟨by rw [mem_ball,Real.dist_eq,sub_zero,abs_of_pos hy.1]; exact hy.2,hy.1⟩)
  obtain ⟨B,b,bd⟩ := bounded_angle_avoiding_one (S := Ioo 0 r) isPreconnected_Ioo
    (fun y hy => (e y hy).1.continuousWithinAt) (fun y hy => (e y hy).2.1)
  refine ⟨B,b,?_⟩
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hr)] with y pos small
  exact ⟨(e y ⟨pos,small⟩).2.2,bd y ⟨pos,small⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_helicoid_axis_phase_bound
