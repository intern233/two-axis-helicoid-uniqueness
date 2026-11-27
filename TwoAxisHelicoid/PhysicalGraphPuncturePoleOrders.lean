import TwoAxisHelicoid.PuncturedNullGaussGrowth
import TwoAxisHelicoid.ArbitraryHelicoidalEndPoles

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology InnerProductSpace
open scoped Topology

/-- In a genuine conformal puncture with single-valued Cartesian
potentials, a physical C¹ normal graph over the helicoid forces the
two exact pole orders. No conformal model of the compact core is used. -/
theorem physical_graph_puncture_double_poles {M : Type*} [TopologicalSpace M] [T2Space M]
    [WeaklyLocallyCompactSpace M] [NoncompactSpace M] (Y : M → Fin 3 → ℝ) (proper : IsProperMap Y)
    (graph : HasHelicoidC1End (coordinateToTube ∘ Y)) (E : PuncturedComplexEnd M) :
    let X := Y ∘ E.coord.symm
    (∀ᶠ z in 𝓝[≠] (0:ℂ), (∀ j, HarmonicAt (fun w => X w j) z) ∧ ConformalCoordinateDerivatives X z ∧
      Function.Injective (fderiv ℝ X z)) →
    (∀ j, ∃ H : ℂ → ℂ, ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt H (immersionComplexCoefficient X z j) z ∧ (H z).re=X z j) →
    (MeromorphicAt (fun z => immersionComplexCoefficient X z 2) 0 ∧
      meromorphicOrderAt (fun z => immersionComplexCoefficient X z 2) 0=(-2:ℤ)) ∧
      MeromorphicAt (immersionGaussLogDerivative X) 0 ∧ meromorphicOrderAt (immersionGaussLogDerivative X) 0=(-2:ℤ) := by
  intro X regular primitive
  let A := coordinateToTube ∘ Y
  let form := immersionComplexCoefficient X
  let g := immersionGaussMap X
  let P := helicoidProjectedComplexParameter ∘ (coordinateToTube ∘ X)
  have apt := coordinateToTube_isProperMap proper
  have met : ∀ᶠ z in 𝓝[≠] (0:ℂ), ContDiffAt ℝ 1 (A ∘ E.coord.symm) z ∧
      ∃ c : ℝ, 0<c ∧ ∀ v : ℂ, (∑ j, (tubeCartesian (fderiv ℝ (A ∘ E.coord.symm) z v) j)^2)=c*‖v‖^2 := by
    filter_upwards [regular] with z r
    have an : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (r.1 j)
    have hd := coordinateToTube.hasFDerivAt.comp z (immersionComplexCoefficient_hasFDerivAt an.differentiableAt)
    have nu := immersionComplexCoefficient_null r.2.1
    refine ⟨coordinateToTube.contDiff.contDiffAt.comp z an.contDiffAt,nullMetric (form z),
      nullMetric_pos nu (immersionComplexCoefficient_regular an.differentiableAt r.2.2),?_⟩
    intro v
    change (∑ j, (tubeCartesian (fderiv ℝ (coordinateToTube ∘ X) z v) j)^2)=_
    rw [hd.fderiv,ContinuousLinearMap.comp_apply,tubeCartesian_coordinateToTube]
    have e := nullRealDerivative_euclidean_norm_sq nu v
    rwa [EuclideanSpace.real_norm_sq_eq] at e
  obtain ⟨smooth,iso⟩ := Filter.eventually_and.mp met
  obtain ⟨H,prim⟩ := primitive 2
  have height : ∀ᶠ z in 𝓝[≠] (0:ℂ), (A (E.coord.symm z)).2=(H z).re+0 :=
    prim.mono (fun z h => h.2.symm.trans (add_zero _).symm)
  obtain ⟨hm,order,dm,do'⟩ := graph.intrinsic_height_orders apt E smooth iso height (prim.mono fun z h => h.1.differentiableAt)
  have agrees := prim.mono (fun _ h => h.1.deriv)
  have hmer : MeromorphicAt (fun z => form z 2) 0 := dm.congr agrees
  have hord : meromorphicOrderAt (fun z => form z 2) 0=(-2:ℤ) := (meromorphicOrderAt_congr agrees).symm.trans do'
  have hneg : meromorphicOrderAt (fun z => form z 2) 0<0 := by rw [hord]; exact_mod_cast (by decide : (-2:ℤ)<0)
  have big := (tendsto_norm_cobounded_atTop.comp (tendsto_cobounded_of_meromorphicOrderAt_neg hneg)).eventually_gt_atTop 0
  obtain ⟨N,_,C,hC,sp⟩ := graph.isothermal_spatial_growth apt E smooth iso
  have component (v : Fin 3 → ℝ) (j : Fin 3) : |v j|≤‖coordinateToTube v‖ := by
    change |v j|≤max (max ‖v 0‖ ‖v 1‖) ‖v 2‖
    simp only [Real.norm_eq_abs]
    fin_cases j
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact le_max_right _ _
  have bd : ∀ᶠ z in 𝓝[≠] (0:ℂ), ∀ j, |X z j|≤2*Real.exp (C/‖z‖^N) :=
    sp.mono (fun z h j => (component (X z) j).trans h)
  obtain ⟨n,F,mer,_,fac⟩ := punctured_null_gauss_meromorphic_of_growth hC bd
    (regular.mono fun _ h => ⟨h.1,h.2.1⟩) primitive hord
  obtain ⟨p,lim,center⟩ := graph.center_puncture_ray apt E
  obtain ⟨u,geo⟩ := graph.eventually_graph_with_slope apt
  have data : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ u (helicoidConformalBase (P z)) ∧
      |u (helicoidConformalBase (P z))|≤1/2 ∧ helicoidGraphGradientNorm u (helicoidConformalBase (P z))≤1/2 ∧
      coordinateToTube (X z)=helicoidGraphMap u (helicoidConformalBase (P z)) ∧ coordinateToTube (X z)∈helicoidTubeEquiv.target := by
    exact E.from_zero.eventually geo
  have same : coordinateToTube ∘ X=ᶠ[𝓝[≠] (0:ℂ)] (helicoidGraphMap u ∘ helicoidConformalBase) ∘ P :=
    data.mono fun _ h => h.2.2.2.1
  have ray : ∀ᶠ t in atTop, ContinuousAt p t ∧ ContinuousAt H (p t) ∧ ContinuousAt F (p t) ∧
      |(H (p t)).re-t|≤1 ∧ (∀ a : ℝ, g (p t)≠(a:ℂ)*exp ((t:ℂ)*I)) ∧ 1/10≤‖g (p t)‖ ∧ ‖g (p t)‖≤10 := by
    filter_upwards [center,lim.eventually data,lim.eventually height,lim.eventually prim,lim.eventually fac,
      lim.eventually regular,lim.eventually big,lim.eventually (punctured_germ_eventually_local same)] with t cen d h hp hf off b loc
    have q : P (p t)=(t:ℂ)*I := cen.2.1
    have base : helicoidConformalBase (P (p t))=(0,t) := by simp [q,helicoidConformalBase]
    have dg := (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (off.1 j)).differentiableAt
    have atHeight : ((coordinateToTube ∘ Y) (E.coord.symm (p t))).2=(H (p t)).re := h.trans (add_zero _)
    refine ⟨cen.1,hp.1.continuousAt,hf.1.continuousAt,by rw [← atHeight]; exact cen.2.2,?_⟩
    exact graph_center_gauss_direction (immersionComplexCoefficient_hasFDerivAt dg) (immersionComplexCoefficient_null off.2.1)
      (norm_pos_iff.mp b) off.2.2 d.2.2.2.2 q (base ▸ d.1) (base ▸ d.2.1) (base ▸ d.2.2.1) loc
  have simple := gauss_factor_simple_from_center_phase (g := g) n lim hm mer order (fac.mono fun _ h => h.2) ray
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
#print axioms TwoAxisHelicoid.physical_graph_puncture_double_poles
