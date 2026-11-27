import TwoAxisHelicoid.ArbitraryTorusGaussMeromorphic
import TwoAxisHelicoid.GaussPhaseSimplePole
import TwoAxisHelicoid.PhysicalCenterPunctureRay
import TwoAxisHelicoid.CenterRulingGaussDifferential

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology InnerProductSpace
open scoped Topology

/-- The actual complex height and the single-valued Gauss logarithm
after removal of its winding factor both have simple poles. -/
theorem arbitrary_helicoidal_torus_logarithmic_end_data (L : PeriodPair) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (proper : IsProperMap Y) (graph : HasHelicoidC1End (coordinateToTube ∘ Y))
    (reg : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L Y) z)) :
    let f := fun z => torusImmersionForms L Y z 2
    let g := fun z => nullGauss (torusImmersionForms L Y z)
    ∃ (n : ℤ) (H F : ℂ → ℂ), MeromorphicAt H 0 ∧ meromorphicOrderAt H 0=((-1:ℤ):WithTop ℤ) ∧
      MeromorphicAt F 0 ∧ meromorphicOrderAt F 0=((-1:ℤ):WithTop ℤ) ∧
      (∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt H (f z) z ∧ (H z).re=puncturedTorusPullback L Y z 2) ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt F (logDeriv g z-(n:ℂ)/z) z ∧ g z=z^n*exp (F z) := by
  let X := puncturedTorusPullback L Y
  let A := coordinateToTube ∘ Y
  let form := torusImmersionForms L Y
  let g := fun z => nullGauss (form z)
  let P := helicoidProjectedComplexParameter ∘ (coordinateToTube ∘ X)
  let := punctured_complex_curve_noncompact (0:PeriodTorus L)
  let : LocallyCompactSpace (PuncturedPeriodTorus L) := ChartedSpace.locallyCompactSpace ℂ _
  have apt := coordinateToTube_isProperMap proper
  obtain ⟨E,coord,smooth,iso⟩ := arbitrary_torus_isothermal_end_chart L Y reg
  obtain ⟨H,prim⟩ := torus_coordinate_puncture_primitive L Y (fun z hz => (reg z hz).1) 2
  have height : ∀ᶠ z in 𝓝[≠] (0:ℂ), (A (E.coord.symm z)).2=(H z).re+0 := by
    filter_upwards [coord,prim] with z e h
    exact (congrArg Prod.snd e).trans (by change X z 2=(H z).re+0; rw [h.2,add_zero])
  obtain ⟨hm,order,_,_⟩ := graph.intrinsic_height_orders apt E smooth iso height (prim.mono fun z h => h.1.differentiableAt)
  obtain ⟨_,hord⟩ := arbitrary_torus_graph_height_pole L Y proper graph reg
  have hneg : meromorphicOrderAt (fun z => form z 2) 0<0 := by rw [hord]; exact_mod_cast (by decide : (-2:ℤ)<0)
  have big := (tendsto_norm_cobounded_atTop.comp (tendsto_cobounded_of_meromorphicOrderAt_neg hneg)).eventually_gt_atTop 0
  obtain ⟨n,F,mer,_,fac⟩ := arbitrary_torus_graph_gauss_meromorphic L Y proper graph reg
  obtain ⟨p,lim,center⟩ := graph.center_puncture_ray apt E
  obtain ⟨u,geo⟩ := graph.eventually_graph_with_slope apt
  have data : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ u (helicoidConformalBase (P z)) ∧
      |u (helicoidConformalBase (P z))|≤1/2 ∧ helicoidGraphGradientNorm u (helicoidConformalBase (P z))≤1/2 ∧
      coordinateToTube (X z)=helicoidGraphMap u (helicoidConformalBase (P z)) ∧ coordinateToTube (X z)∈helicoidTubeEquiv.target := by
    filter_upwards [E.from_zero.eventually geo,coord] with z h e
    change A (E.coord.symm z)=coordinateToTube (X z) at e
    let S := fun v : HelicoidTubeCoordinates =>
      let q := helicoidConformalBase (helicoidProjectedComplexParameter v)
      DifferentiableAt ℝ u q ∧ |u q|≤1/2 ∧ helicoidGraphGradientNorm u q≤1/2 ∧
        v=helicoidGraphMap u q ∧ v∈helicoidTubeEquiv.target
    exact (congrArg S e).mp h
  have same : coordinateToTube ∘ X=ᶠ[𝓝[≠] (0:ℂ)] (helicoidGraphMap u ∘ helicoidConformalBase) ∘ P :=
    data.mono fun _ h => h.2.2.2.1
  have ray : ∀ᶠ t in atTop, ContinuousAt p t ∧ ContinuousAt H (p t) ∧ ContinuousAt F (p t) ∧
      |(H (p t)).re-t|≤1 ∧ (∀ a : ℝ, g (p t)≠(a:ℂ)*exp ((t:ℂ)*I)) ∧ 1/10≤‖g (p t)‖ ∧ ‖g (p t)‖≤10 := by
    filter_upwards [center,lim.eventually data,lim.eventually coord,lim.eventually height,lim.eventually prim,lim.eventually fac,
      lim.eventually (punctured_lattice_regular_near_zero L),lim.eventually big,lim.eventually (punctured_germ_eventually_local same)] with t cen d c h hp hf off b loc
    have q : P (p t)=(t:ℂ)*I := (congrArg helicoidProjectedComplexParameter c).symm.trans cen.2.1
    have base : helicoidConformalBase (P (p t))=(0,t) := by simp [q,helicoidConformalBase]
    have dg := (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt ((reg _ off).1 j)).differentiableAt
    have atHeight : ((coordinateToTube ∘ Y) (E.coord.symm (p t))).2=(H (p t)).re := h.trans (add_zero _)
    refine ⟨cen.1,hp.1.continuousAt,hf.1.continuousAt,by rw [← atHeight]; exact cen.2.2,?_⟩
    exact graph_center_gauss_direction (immersionComplexCoefficient_hasFDerivAt dg) (immersionComplexCoefficient_null (reg _ off).2.1)
      (norm_pos_iff.mp b) (reg _ off).2.2 d.2.2.2.2 q (base ▸ d.1) (base ▸ d.2.1) (base ▸ d.2.2.1) loc
  have simple := gauss_factor_simple_from_center_phase (g := g) n lim hm mer order (fac.mono fun _ h => h.2) ray
  exact ⟨n,H,F,hm,order,mer,simple,prim,fac⟩

/-- For any regular harmonic conformal marked torus with one proper
physical C¹ helicoidal end both Weierstrass logarithmic differentials
have the exact double pole. The compact part may be immersed and the
surface need not contain any straight line. -/
theorem arbitrary_helicoidal_torus_two_double_poles (L : PeriodPair) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (proper : IsProperMap Y) (graph : HasHelicoidC1End (coordinateToTube ∘ Y))
    (reg : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L Y) z)) :
    let f := fun z => torusImmersionForms L Y z 2
    let g := fun z => nullGauss (torusImmersionForms L Y z)
    (MeromorphicAt f 0 ∧ meromorphicOrderAt f 0=((-2:ℤ):WithTop ℤ)) ∧
    (MeromorphicAt (logDeriv g) 0 ∧ meromorphicOrderAt (logDeriv g) 0=((-2:ℤ):WithTop ℤ)) := by
  let g := fun z => nullGauss (torusImmersionForms L Y z)
  obtain ⟨n,H,F,_,_,mer,simple,_,fac⟩ := arbitrary_helicoidal_torus_logarithmic_end_data L Y proper graph reg
  obtain ⟨hmer,hord⟩ := arbitrary_torus_graph_height_pole L Y proper graph reg
  have ord := meromorphicOrderAt_deriv_eq_sub_one (𝕜 := ℂ) (n := (-1:ℤ)) (by norm_num) simple
  let k := fun z : ℂ => (n:ℂ)/z
  have km : MeromorphicAt k 0 := (MeromorphicAt.const (n:ℂ) 0).div analyticAt_id.meromorphicAt
  have ko : meromorphicOrderAt (deriv F) 0<meromorphicOrderAt k 0 := by
    rw [ord]
    by_cases nz : (n:ℂ)=0
    · have zero : k=(fun _ : ℂ => (0:ℂ)) := by funext z; simp [k,nz]
      simp only [zero,meromorphicOrderAt_const,↓reduceIte]
      exact WithTop.coe_lt_top _
    · change _<meromorphicOrderAt ((fun _ : ℂ => (n:ℂ))/(id : ℂ → ℂ)) 0
      rw [meromorphicOrderAt_div (MeromorphicAt.const (n:ℂ) 0) analyticAt_id.meromorphicAt,meromorphicOrderAt_const,meromorphicOrderAt_id]
      simp only [nz,↓reduceIte]
      change ((-2:ℤ) : WithTop ℤ)<((-1:ℤ) : WithTop ℤ)
      exact WithTop.coe_lt_coe.mpr (by decide)
  have germ : (deriv F+k)=ᶠ[𝓝[≠] (0:ℂ)] logDeriv g :=
    fac.mono fun z h => by change deriv F z+(n:ℂ)/z=logDeriv g z; rw [h.1.deriv,sub_add_cancel]
  exact ⟨⟨hmer,hord⟩,(mer.deriv.add km).congr germ,(meromorphicOrderAt_congr germ).symm.trans ((meromorphicOrderAt_add_eq_left_of_lt km ko).trans ord)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.arbitrary_helicoidal_torus_logarithmic_end_data
#print axioms TwoAxisHelicoid.arbitrary_helicoidal_torus_two_double_poles
