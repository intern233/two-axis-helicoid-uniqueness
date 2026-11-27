import TwoAxisHelicoid.AmbientHarmonicImmersion
import TwoAxisHelicoid.ArbitraryHelicoidalEndPoles
import TwoAxisHelicoid.WindingHeightNormalForm
import TwoAxisHelicoid.UnitHeightPullback
import TwoAxisHelicoid.MarkedTorusExteriorHeightChart

namespace TwoAxisHelicoid
open Complex Set Filter Bornology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- The physical graph yields a genuine exterior height chart on the
marked torus, with its integer winding and complex leading coefficient
still visible. All formulas concern the same original immersion. -/
theorem arbitrary_torus_winding_height_chart (L : PeriodPair) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (proper : IsProperMap Y) (graph : HasHelicoidC1End (coordinateToTube ∘ Y))
    (reg : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L Y) z)) :
    ∃ (e : OpenPartialHomeomorph (PuncturedPeriodTorus L) ℂ) (R : ℝ) (m : ℤ) (c : ℂ) (B : ℂ → ℂ),
       0<R ∧ e.target={w : ℂ | R<‖w‖} ∧ IsCompact e.sourceᶜ ∧
       e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (PuncturedPeriodTorus L) ∧ (∀ x∈e.source, Y x 2=(e x).re) ∧
       c≠0 ∧ AnalyticAt ℂ B 0 ∧ B 0≠0 ∧
       ∀ᶠ w in cobounded ℂ, let g := w^m*exp (c*w)*B w⁻¹
         immersionGaussMap (Y ∘ e.symm) w=g ∧ HasFDerivAt (Y ∘ e.symm) (nullRealDerivative (weierstrassTriple g 1)) w := by
  let X := puncturedTorusPullback L Y
  obtain ⟨n,H,F,hm,ho,fm,fo,prim,factor⟩ := arbitrary_helicoidal_torus_logarithmic_end_data L Y proper graph reg
  obtain ⟨k,B,c,ka,_,kl,ba,bn,cn,left,right⟩ := winding_height_normal_form hm fm ho fo (factor.mono fun _ h => h.2)
  let K := fun w : ℂ => k w⁻¹
  have inf : Tendsto (fun w : ℂ => w⁻¹) (cobounded ℂ) (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_inv₀_cobounded,?_⟩
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with w hw
    exact inv_ne_zero (norm_pos_iff.mp hw)
  have Klim : Tendsto K (cobounded ℂ) (𝓝[≠] 0) := kl.comp inf
  have anal : ∀ᶠ w in cobounded ℂ, AnalyticAt ℂ K w := by
    filter_upwards [inf.eventually (ka.eventually_analyticAt.filter_mono nhdsWithin_le_nhds),tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with w h n
    exact h.comp (analyticAt_id.inv (norm_pos_iff.mp n))
  have data : ∀ᶠ w in cobounded ℂ, H (K w)=w ∧ immersionGaussMap X (K w)=w^(-n)*exp (c*w)*B w⁻¹ := by
    filter_upwards [inf.eventually right] with w h
    change H (k w⁻¹)=w ∧ nullGauss (torusImmersionForms L Y (k w⁻¹))=_
    simpa only [inv_inv,inv_zpow,zpow_neg,div_inv_eq_mul] using h
  have Hesc := tendsto_cobounded_of_meromorphicOrderAt_neg (show meromorphicOrderAt H 0<0 by rw [ho]; exact_mod_cast (by decide : (-1:ℤ)<0))
  have regular := Klim.eventually (punctured_lattice_regular_near_zero L)
  have vals := (data.and (Klim.eventually prim)).and regular
  obtain ⟨M,_,all⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp vals
  obtain ⟨z,hz⟩ := (punctured_lattice_regular_near_zero L).exists
  obtain ⟨e,R,rp,far,target,core,hol,proj⟩ := marked_torus_exterior_height_chart L (puncturedPlaneProjection L ⟨z,hz⟩) H K
    Hesc Klim left (data.mono fun _ h => h.1) hm.eventually_analyticAt anal M
  have outside {w : ℂ} (hw : w∈e.target) : M≤‖w‖ := far.le.trans (show R<‖w‖ by simpa only [target,mem_ofPred_eq] using hw).le
  have pos {w : ℂ} (hw : w∈e.target) : Y (e.symm w)=X (K w) := by
    have off := (all (outside hw)).2
    have q : e.symm w=puncturedPlaneProjection L ⟨K w,off⟩ := Subtype.ext (proj w hw)
    rw [q]
    simp [X,puncturedTorusPullback,off]
  have ht (x : PuncturedPeriodTorus L) (hx : x∈e.source) : Y x 2=(e x).re := by
    have hw := e.map_source hx
    obtain ⟨⟨v,_⟩,p⟩ := (all (outside hw)).1
    have h := congrFun (pos hw) 2
    rw [e.left_inv hx] at h
    exact h.trans (p.2.symm.trans (congrArg Complex.re v))
  refine ⟨e,R,-n,c,B,rp,target,core,hol,ht,cn,ba,bn,?_⟩
  have same : Y ∘ e.symm=ᶠ[cobounded ℂ] X ∘ K := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop R] with w hw
    exact pos (target ▸ hw)
  have inverse : H ∘ K=ᶠ[cobounded ℂ] id := data.mono fun _ h => h.1
  filter_upwards [vals,anal,complex_cobounded_eventuallyEq_nhds same,complex_cobounded_eventuallyEq_nhds inverse] with w facts kA eq inv
  obtain ⟨⟨⟨_,gw⟩,hp⟩,off⟩ := facts
  have d : DifferentiableAt ℝ X (K w) := (spatial_harmonic_of_coordinates (reg _ off).1).1.differentiableAt two_ne_zero
  obtain ⟨dx,gauss⟩ := inverse_height_pullback_weierstrass d (reg _ off).2.1 kA.differentiableAt hp.1 inv
  have form : immersionComplexCoefficient (Y ∘ e.symm) w=immersionComplexCoefficient (X ∘ K) w := by
    funext j
    unfold immersionComplexCoefficient scalarComplexCoefficient
    have h : (fun a => (Y ∘ e.symm) a j)=ᶠ[𝓝 w] fun a => (X ∘ K) a j := eq.mono fun a v => congrFun v j
    rw [h.fderiv_eq]
  exact ⟨(congrArg nullGauss form).trans (gauss.trans gw),gw ▸ dx.congr_of_eventuallyEq eq⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.arbitrary_torus_winding_height_chart
