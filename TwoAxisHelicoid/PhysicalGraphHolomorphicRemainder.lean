import TwoAxisHelicoid.MeasuredDoublePolePrimitives
import TwoAxisHelicoid.PunctureHeightChartComposition
import TwoAxisHelicoid.PhysicalGraphWindingElimination
import TwoAxisHelicoid.WindingHeightNormalForm
import TwoAxisHelicoid.UnitHeightPullback
import TwoAxisHelicoid.HeightInverseRegularity

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology Topology
open scoped Topology ContDiff Manifold

/-- On an actual physical graph end, the two double poles and a
single-valued physical height primitive force the holomorphic
logarithmic remainder of Proposition 2.1. This argument takes place in
the given chart of the same surface and uses no marked torus or axis. -/
theorem physical_graph_holomorphic_log_remainder {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {X : M → Fin 3 → ℝ} (cx : Continuous X) (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (graph : HasHelicoidC1End (coordinateToTube ∘ X)) (A : GeometricDoublePoleEnd X)
    {H : ℂ → ℂ} (prim : ∀ᶠ z in 𝓝[≠] (0:ℂ),
      HasDerivAt H (immersionComplexCoefficient (X ∘ A.endChart.coord.symm) z 2) z ∧
      (H z).re=X (A.endChart.coord.symm z) 2) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ),
      immersionGaussLogDerivative (X ∘ A.endChart.coord.symm) z-
        I*immersionComplexCoefficient (X ∘ A.endChart.coord.symm) z 2=Q z := by
  let E := A.endChart
  let Y := X ∘ E.coord.symm
  let g := immersionGaussMap Y
  let h := fun z => immersionComplexCoefficient Y z 2
  have domain : ∀ᶠ z in 𝓝[≠] (0:ℂ), z∈E.coord.target := by
    change E.coord.target∈𝓝[≠] (0:ℂ)
    rw [E.target_eq]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) E.radius_pos)) self_mem_nhdsWithin
  have chart := harmonic_immersion_chart_maximal charts A.holomorphic
  have hn : ∀ᶠ z in 𝓝[≠] (0:ℂ), h z≠0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero A.height).mp (by rw [A.heightOrder]; decide)
  have reg : ∀ᶠ z in 𝓝[≠] (0:ℂ), AnalyticAt ℂ g z ∧ g z≠0 := by
    filter_upwards [domain,hn] with z hz non
    have c := chart z hz
    have an (j : Fin 3) : AnalyticAt ℂ (fun w => immersionComplexCoefficient Y w j) z :=
      scalarComplexCoefficient_analyticAt (c.1 j)
    have null := immersionComplexCoefficient_null c.2.1
    exact ⟨nullGauss_analyticAt_of_height an null non,nullGauss_ne_zero_of_height null non⟩
  obtain ⟨hm,ho,n,F,fm,fo,fac⟩ := logarithmic_factors_of_measured_double_poles (g:=g)
    A.height A.heightOrder A.gauss A.gaussOrder reg (prim.mono fun _ p => p.1)
  obtain ⟨k,B,c,ka,k0,kl,ba,bn,cn,left,right⟩ := winding_height_normal_form hm fm ho fo fac
  let K := fun w : ℂ => k w⁻¹
  have inf : Tendsto (Inv.inv : ℂ → ℂ) (cobounded ℂ) (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_inv₀_cobounded,?_⟩
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with w hw
    exact inv_ne_zero (norm_pos_iff.mp hw)
  have klim : Tendsto K (cobounded ℂ) (𝓝[≠] 0) := kl.comp inf
  have fact : ∀ᶠ w in cobounded ℂ, H (K w)=w ∧ g (K w)=w^(-n)*exp (c*w)*B w⁻¹ := by
    filter_upwards [inf.eventually right] with w co
    simpa only [K,inv_inv,inv_zpow,zpow_neg,div_inv_eq_mul] using co
  obtain ⟨d,R,rp,target,tail,sub,_,fw,bw,ad,ai⟩ := punctured_height_exterior_chart ka k0 klim
    (hm.eventually_analyticAt.and left) (fact.mono fun _ p => p.1)
    (domain.and (prim.mono fun _ p => p.2)) (univ_mem (f:=cobounded ℂ))
  let e := E.coord.trans d
  have composed := E.compose_holomorphic_end_chart A.holomorphic d tail (fun _ p => (sub p).1) ad ai
  have et : e.target={w : ℂ | R<‖w‖} := composed.1.trans target
  have height (x : M) (hx : x∈e.source) : X x 2=(e x).re := by
    have q := (sub hx.2).2
    change (H (E.coord x)).re=X (E.coord.symm (E.coord x)) 2 at q
    change X x 2=(d (E.coord x)).re
    rw [E.coord.left_inv hx.1,← fw] at q
    exact q.symm
  have dt : d.target∈cobounded ℂ := by
    rw [target]
    exact tendsto_norm_cobounded_atTop.eventually_gt_atTop R
  have inverse : H ∘ K =ᶠ[cobounded ℂ] id := fact.mono fun _ p => p.1
  have same : X ∘ e.symm =ᶠ[cobounded ℂ] Y ∘ K := .of_forall (fun w => congrArg Y (bw w))
  have measured : ∀ᶠ w in cobounded ℂ, HasFDerivAt (X ∘ e.symm)
      (nullRealDerivative (weierstrassTriple (w^(-n)*exp (c*w)*B w⁻¹) 1)) w := by
    filter_upwards [dt,klim.eventually prim,klim.eventually domain,fact,
      complex_cobounded_eventuallyEq_nhds inverse,complex_cobounded_eventuallyEq_nhds same] with w hw hp hz gval inv pos
    have y := chart (K w) hz
    have dy : DifferentiableAt ℝ Y (K w) :=
      (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (y.1 j)).differentiableAt
    have kA : DifferentiableAt ℂ K w := (show (d.symm : ℂ → ℂ)=K from funext bw) ▸ (ai w hw).differentiableAt
    have pair := inverse_height_pullback_weierstrass dy y.2.1 kA hp.1 inv
    exact gval.2 ▸ pair.1.congr_of_eventuallyEq pos
  obtain ⟨coeff,number⟩ := physical_graph_winding_elimination graph cx e et height (-n) cn ba.continuousAt bn measured
  have Hlim := tendsto_cobounded_of_meromorphicOrderAt_neg (show meromorphicOrderAt H 0<0 by
    rw [ho]; exact_mod_cast (by decide : (-1:ℤ)<0))
  apply logarithmic_remainder_after_winding_elimination hm ho ba bn (prim.mono fun _ p => p.1)
  filter_upwards [left,Hlim.eventually fact] with z inv gf
  change k (H z)⁻¹=z at inv
  simpa only [K,inv,number,coeff,zpow_zero,one_mul] using gf.2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_graph_holomorphic_log_remainder
