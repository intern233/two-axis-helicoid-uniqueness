import TwoAxisHelicoid.ExteriorComplexEnd
import TwoAxisHelicoid.HeightGaussEndNormalForm
import TwoAxisHelicoid.HolomorphicImmersionCoordinateChange

namespace TwoAxisHelicoid
open Complex Filter Set Bornology Topology
open scoped Topology ContDiff Manifold

/-- Starting in the exterior height coordinate itself, reciprocation gives
the two actual order-minus-two one-forms at the added point. -/
theorem actual_exterior_height_gauss_poles (Y : ℂ → Fin 3 → ℝ) (b α : ℝ) (hα : α ≠ 0)
    (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (hreg : ∀ᶠ ζ in cobounded ℂ, DifferentiableAt ℝ Y ζ)
    (hh : ∀ᶠ ζ in cobounded ℂ, Y ζ 2 = b+ζ.re)
    (hg : ∀ᶠ ζ in cobounded ℂ, immersionGaussMap Y ζ = Complex.exp (I*(α:ℂ)*ζ+F ζ⁻¹)) :
    let Z := fun w : ℂ => Y w⁻¹
    MeromorphicAt (fun w => immersionComplexCoefficient Z w 2) 0 ∧
      meromorphicOrderAt (fun w => immersionComplexCoefficient Z w 2) 0 = -2 ∧
      MeromorphicAt (immersionGaussLogDerivative Z) 0 ∧
      meromorphicOrderAt (immersionGaussLogDerivative Z) 0 = -2 := by
  let Z := fun w : ℂ => Y w⁻¹
  apply height_gauss_normal_form_actual_double_poles Z b α hα F hF
  · exact tendsto_inv₀_nhdsNE_zero.eventually hh
  · filter_upwards [tendsto_inv₀_nhdsNE_zero.eventually hg,tendsto_inv₀_nhdsNE_zero.eventually hreg,
      self_mem_nhdsWithin] with w hw hr hn
    change w ≠ 0 at hn
    have hswap : immersionGaussMap Z w = immersionGaussMap Y w⁻¹ :=
      immersionGaussMap_comp_holomorphic hr (hasDerivAt_inv hn) (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hn)))
    rw [hswap,hw,inv_inv,div_eq_mul_inv]

/-- When two spatial maps agree off the compactifying point, all their
actual differential coefficients and their Gauss logarithmic derivatives
agree there as punctured germs. -/
theorem spatial_equal_germ_end_coefficients {X Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (he : X =ᶠ[𝓝[≠] z] Y) :
    immersionComplexCoefficient X =ᶠ[𝓝[≠] z] immersionComplexCoefficient Y ∧
      immersionGaussLogDerivative X =ᶠ[𝓝[≠] z] immersionGaussLogDerivative Y := by
  have hc : immersionComplexCoefficient X =ᶠ[𝓝[≠] z] immersionComplexCoefficient Y := by
    filter_upwards [punctured_germ_eventually_local he] with w hw
    funext j
    have hj : (fun v => X v j) =ᶠ[𝓝 w] (fun v => Y v j) := hw.fun_comp (fun a => a j)
    unfold immersionComplexCoefficient scalarComplexCoefficient
    rw [hj.fderiv_eq]
  have hg : immersionGaussMap X =ᶠ[𝓝[≠] z] immersionGaussMap Y := hc.fun_comp nullGauss
  refine ⟨hc,?_⟩
  filter_upwards [punctured_germ_eventually_local hg] with w hw
  unfold immersionGaussLogDerivative
  rw [hw.deriv_eq,hw.self_of_nhds]

/-- The exact exterior height and Gauss normal form gives the two double
poles in the actual disk chart at infinity on the compactified original
surface, irrespective of the value one chooses to fill into the spatial
map at the puncture. -/
theorem compactified_exterior_surface_end_poles {M : Type*} [TopologicalSpace M] [T2Space M]
    [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    (X : M → Fin 3 → ℝ) (e : OpenPartialHomeomorph M ℂ) {R : ℝ} (hR : 0 < R)
    (ht : e.target = {ζ : ℂ | R < ‖ζ‖}) (hcore : IsCompact e.sourceᶜ)
    (hesc : Tendsto (fun x => ‖e x‖) (cocompact M) atTop)
    (b α : ℝ) (hα : α ≠ 0) (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (hreg : ∀ᶠ ζ in cobounded ℂ, DifferentiableAt ℝ (X ∘ e.symm) ζ)
    (hh : ∀ᶠ ζ in cobounded ℂ, X (e.symm ζ) 2 = b+ζ.re)
    (hg : ∀ᶠ ζ in cobounded ℂ, immersionGaussMap (X ∘ e.symm) ζ = Complex.exp (I*(α:ℂ)*ζ+F ζ⁻¹))
    (a : Fin 3 → ℝ) :
    let E := exteriorCoordinateComplexEnd e hR ht hcore hesc
    let Z := fun w : ℂ => (E.filledChart.symm w).elim a X
    MeromorphicAt (fun w => immersionComplexCoefficient Z w 2) 0 ∧
      meromorphicOrderAt (fun w => immersionComplexCoefficient Z w 2) 0 = -2 ∧
      MeromorphicAt (immersionGaussLogDerivative Z) 0 ∧
      meromorphicOrderAt (immersionGaussLogDerivative Z) 0 = -2 := by
  let E := exteriorCoordinateComplexEnd e hR ht hcore hesc
  let Z := fun w : ℂ => (E.filledChart.symm w).elim a X
  let Y := fun w : ℂ => X (e.symm w⁻¹)
  have he : Z =ᶠ[𝓝[≠] (0:ℂ)] Y := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    change w ≠ 0 at hw
    change (E.filledInverse w).elim a X = _
    rw [PuncturedComplexEnd.filledInverse,ite_eq_right_iff.mpr (fun h => (hw h).elim)]
    rfl
  obtain ⟨hc,hg'⟩ := spatial_equal_germ_end_coefficients he
  have h₂ := hc.fun_comp (fun v : Fin 3 → ℂ => v 2)
  obtain ⟨hd,ho,hm,ho'⟩ := actual_exterior_height_gauss_poles (X ∘ e.symm) b α hα F hF hreg hh hg
  exact ⟨hd.congr h₂.symm,(meromorphicOrderAt_congr h₂).trans ho,hm.congr hg'.symm,
    (meromorphicOrderAt_congr hg').trans ho'⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compactified_exterior_surface_end_poles
