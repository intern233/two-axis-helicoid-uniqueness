import TwoAxisHelicoid.MarkedHelicoidAxisPhase

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology
open scoped Topology

/-- Properness along the actual vertical axis forces the absolute physical
height to tend to infinity at the upper imaginary parameter ray. -/
theorem marked_helicoid_axis_height_escape {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (proper : IsProperMap (harmonicTorusImmersion hX)) :
    Tendsto (fun y : ℝ => |X ((y:ℂ)*I) 2|) (𝓝[>] (0:ℝ)) atTop := by
  let L := rhombicPeriodPair t ht
  obtain ⟨E,chart,_,_⟩ := hX.standard_end_chart
  have esc := tendsto_norm_cocompact_atTop.comp ((isProperMap_iff_tendsto_cocompact.mp (coordinateToTube_isProperMap proper)).2.comp E.from_zero)
  have plane : Tendsto (fun z => ‖coordinateToTube (X z)‖) (𝓝[≠] (0:ℂ)) atTop :=
    esc.congr' (chart.mono fun _ h => congrArg norm h)
  apply (plane.comp positive_imaginary_ray_tendsto).congr'
  filter_upwards [positive_imaginary_ray_tendsto.eventually (punctured_lattice_regular_near_zero L)] with y reg
  have ax := hX.vertical_axis_zero reg (by simp [Complex.mul_re])
  change max (max ‖X _ 0‖ ‖X _ 1‖) ‖X _ 2‖=|X _ 2|
  rw [ax.1,ax.2]
  simp [Real.norm_eq_abs]

/-- Both complex end coefficients of an actual proper marked two-axis
helicoidal C¹ immersion are meromorphic with exact order minus two.
In particular no asymptotic formula for the Gauss map or its derivative
is required. -/
theorem marked_helicoid_two_double_poles {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (proper : IsProperMap (harmonicTorusImmersion hX))
    (graph : HasHelicoidC1End (coordinateToTube ∘ harmonicTorusImmersion hX)) :
    let p := puncturedImmersionCoefficient (rhombicPeriodPair t ht) X
    let h := fun z => p z 2
    let g := fun z => nullGauss (p z)
    (MeromorphicAt h 0 ∧ meromorphicOrderAt h 0=((-2:ℤ):WithTop ℤ)) ∧
    (MeromorphicAt (logDeriv g) 0 ∧ meromorphicOrderAt (logDeriv g) 0=((-2:ℤ):WithTop ℤ)) := by
  let L := rhombicPeriodPair t ht
  let p := puncturedImmersionCoefficient L X
  let g := fun z => nullGauss (p z)
  let j := fun y : ℝ => (y:ℂ)*I
  obtain ⟨F,mer,logF⟩ := marked_helicoid_meromorphic_gauss_log ht hX proper graph
  obtain ⟨B,hB,phase⟩ := marked_helicoid_axis_phase_bound ht hX proper graph
    (logF.mono fun _ h => ⟨h.1.differentiableAt,h.2⟩)
  have clos : ∀ᶠ y in 𝓝[>] (0:ℝ), |X (j y) 2|≤‖F (j y)‖+B ∧ ‖F (j y)‖≤|X (j y) 2|+B := by
    filter_upwards [phase] with y h
    rcases h with ⟨n,d⟩
    rw [n]
    have a := abs_abs_sub_abs_le_abs_sub (F (j y)).im (X (j y) 2)
    have b := abs_le.mp (a.trans d)
    exact ⟨by linarith [b.1],by linarith [b.2]⟩
  have esc : Tendsto (fun y => ‖F (j y)‖) (𝓝[>] (0:ℝ)) atTop := by
    refine tendsto_atTop.mpr fun a => ?_
    filter_upwards [clos,(marked_helicoid_axis_height_escape ht hX proper).eventually_ge_atTop (a+B)] with y h e
    change a+B≤|X (j y) 2| at e
    linarith [h.1]
  obtain ⟨C,radius⟩ := marked_helicoid_height_radius_bound ht hX proper graph
  have bound : ∀ᶠ y in 𝓝[>] (0:ℝ), ‖j y‖*‖F (j y)‖≤C+B := by
    filter_upwards [clos,positive_imaginary_ray_tendsto.eventually radius,
      positive_imaginary_ray_tendsto.eventually (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) zero_lt_one))] with y h e small
    have sy : ‖j y‖≤1 := (show ‖j y‖<1 by simpa only [mem_ball,dist_zero_right] using small).le
    calc
      _ ≤ ‖j y‖*(|X (j y) 2|+B) := mul_le_mul_of_nonneg_left h.2 (norm_nonneg _)
      _ ≤ C+B := by rw [mul_add]; exact add_le_add e ((mul_le_mul_of_nonneg_right sy hB).trans_eq (one_mul _))
  have simple := meromorphic_order_simple_of_ray positive_imaginary_ray_tendsto mer esc ⟨C+B,bound⟩
  have order := meromorphicOrderAt_deriv_eq_sub_one (𝕜 := ℂ) (n := (-1:ℤ)) (by norm_num) simple
  have germs : deriv F =ᶠ[𝓝[≠] (0:ℂ)] logDeriv g := logF.mono fun _ h => h.1.deriv
  exact ⟨marked_helicoid_height_double_pole ht hX proper graph,mer.deriv.congr germs,
    (meromorphicOrderAt_congr germs).symm.trans order⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_helicoid_two_double_poles
