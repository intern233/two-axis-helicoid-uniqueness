import TwoAxisHelicoid.MarkedTorusExteriorHeightChart
import TwoAxisHelicoid.HarmonicAxisIntersectionPoint
import TwoAxisHelicoid.OriginalExteriorTorusReduction

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology ContDiff Manifold

private theorem immersion_coefficient_of_null_derivative {Y : ℂ → Fin 3 → ℝ} {z : ℂ} {p : Fin 3 → ℂ}
    (h : HasFDerivAt Y (nullRealDerivative p) z) : immersionComplexCoefficient Y z = p := by
  have hd := (immersionComplexCoefficient_hasFDerivAt h.differentiableAt).unique h
  funext j
  apply Complex.ext
  · simpa only [nullRealDerivative_apply,one_mul] using congrArg (fun L : ℂ →L[ℝ] (Fin 3 → ℝ) => L 1 j) hd
  · simpa only [nullRealDerivative_apply,Complex.I_mul_re,neg_inj] using congrArg (fun L : ℂ →L[ℝ] (Fin 3 → ℝ) => L I j) hd

private theorem nullGauss_weierstrass_unit_height (g : ℂ) : nullGauss (weierstrassTriple g 1) = g := by
  change 1 / ((g⁻¹-g)/2*1-I*(I*(g⁻¹+g)/2*1)) = g
  have he : (g⁻¹-g)/2*1-I*(I*(g⁻¹+g)/2*1) = g⁻¹ := by
    linear_combination -((g⁻¹+g)/2)*Complex.I_sq
  rw [he,one_div,inv_inv]

/-- Construct the actual biholomorphic exterior Weierstrass chart on any
integer branch of the original rhombic torus. A fixed quarter-turn is the
only spatial change of coordinates. -/
theorem harmonic_integer_geometric_exterior {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    (hc : c ≠ 0) (m : ℤ) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    Nonempty (GeometricExteriorCoordinate (verticalRotation I ∘ harmonicTorusImmersion hX)) := by
  let L := rhombicPeriodPair t ht
  let α := 2*(a-(m:ℝ))/c
  let H := actualComplexHeight t a c ht
  have hXd := harmonic_integer_gauss_data_has_coordinate_differential ht ha hc m hX hh hg
  obtain ⟨K,f,b,R,hK,hf,_,hle,hdata⟩ := integer_primitive_analytic_height_end_coordinate m ht ha hc hXd
  have hr : ∀ᶠ ξ in cobounded ℂ, H (K ξ) = ξ := by
    filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with ξ hξ
    exact (hdata ξ hξ).1
  have hKa := actual_height_inverse_eventually_analytic ht hc hK hr
  have hHa : ∀ᶠ z in 𝓝[≠] (0:ℂ), AnalyticAt ℂ H z := by
    filter_upwards [rhombic_puncture_eventually_off_lattice ht] with z hz
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with y hy
    exact (actualComplexHeight_hasDerivAt ht hy).differentiableAt
  obtain ⟨B,_,hB⟩ := hasBasis_cobounded_norm.eventually_iff.mp (hK.eventually (rhombic_puncture_eventually_off_lattice ht))
  obtain ⟨e,R',hR',hBR,htarget,hcore,he,hinv⟩ := marked_torus_exterior_height_chart L (rhombicAxisPoint ht)
    H K (actualComplexHeight_tendsto (a := a) ht hc) hK hle hr hHa hKa (max B R)
  let Z := verticalRotation I ∘ harmonicTorusImmersion hX
  have far {ξ : ℂ} (hξ : ξ ∈ e.target) : max B R < ‖ξ‖ := by
    rw [htarget] at hξ
    exact hBR.trans hξ
  have heq {ξ : ℂ} (hξ : ξ ∈ e.target) : Z (e.symm ξ) = verticalRotation I (X (K ξ)) := by
    have hn := hB ((le_max_left B R).trans (far hξ).le)
    have hx : e.symm ξ = ⟨periodTorusProjection L (K ξ),fun h => hn ((periodTorusProjection_eq_zero L _).mp h)⟩ :=
      Subtype.ext (hinv ξ hξ)
    change verticalRotation I (harmonicTorusImmersion hX (e.symm ξ)) = _
    rw [hx,harmonicTorusImmersion_projection hX hn]
  refine ⟨⟨e,R',hR',htarget,hcore,he,b,?_,α,integer_helicoidal_pitch_ne_zero ha hc m,f,hf,?_⟩⟩
  · intro x hx
    have ht' := e.map_source hx
    have h := congrFun (heq ht') 2
    rw [e.left_inv hx] at h
    exact h.trans ((hdata (e x) ((le_max_right _ _).trans_lt (far ht'))).2.2.trans (add_comm _ _))
  · filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R')] with ξ hξ
    have hx : ξ ∈ e.target := htarget ▸ hξ
    have hD := (hdata ξ ((le_max_right _ _).trans_lt (far hx))).2.1
    have hD' : HasFDerivAt (Z ∘ e.symm) _ ξ := hD.congr_of_eventuallyEq (by
      filter_upwards [e.open_target.mem_nhds hx] with y hy
      exact heq hy)
    exact (congrArg nullGauss (immersion_coefficient_of_null_derivative hD')).trans
      (nullGauss_weierstrass_unit_height _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_integer_geometric_exterior
