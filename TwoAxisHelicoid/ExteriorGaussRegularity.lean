import TwoAxisHelicoid.ExteriorHeightGaussPoles

namespace TwoAxisHelicoid
open Bornology Complex Set Filter Topology
open scoped Topology OnePoint

/-- The exterior immersion and its actual Gauss map are differentiable in
the finite part of the filled end chart. The Gauss regularity follows from
the holomorphic exponential formula on a punctured neighborhood. -/
theorem compactified_exterior_end_regular {M : Type*} [TopologicalSpace M] [T2Space M]
    [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    (X : M → Fin 3 → ℝ) (e : OpenPartialHomeomorph M ℂ) {R : ℝ} (hR : 0 < R)
    (ht : e.target = {ζ : ℂ | R < ‖ζ‖}) (hcore : IsCompact e.sourceᶜ)
    (hesc : Tendsto (fun x => ‖e x‖) (cocompact M) atTop)
    (α : ℝ) (F : ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (hreg : ∀ᶠ ζ in cobounded ℂ, DifferentiableAt ℝ (X ∘ e.symm) ζ)
    (hg : ∀ᶠ ζ in cobounded ℂ, immersionGaussMap (X ∘ e.symm) ζ = Complex.exp (I*(α:ℂ)*ζ+F ζ⁻¹))
    (a : Fin 3 → ℝ) :
    let E := exteriorCoordinateComplexEnd e hR ht hcore hesc
    let Z := fun w : ℂ => (E.filledChart.symm w).elim a X
    ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ Z w ∧ DifferentiableAt ℂ (immersionGaussMap Z) w := by
  let E := exteriorCoordinateComplexEnd e hR ht hcore hesc
  let Z := fun w : ℂ => (E.filledChart.symm w).elim a X
  let Y := fun w : ℂ => X (e.symm w⁻¹)
  have he : Z =ᶠ[𝓝[≠] (0:ℂ)] Y := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    change w ≠ 0 at hw
    change (E.filledInverse w).elim a X = _
    rw [PuncturedComplexEnd.filledInverse,ite_eq_right_iff.mpr (fun h => (hw h).elim)]
    rfl
  have hrc := tendsto_inv₀_nhdsNE_zero.eventually hreg
  have hy : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ Z w := by
    filter_upwards [punctured_germ_eventually_local he,hrc,self_mem_nhdsWithin] with w hw hr hn
    change w ≠ 0 at hn
    exact (hr.comp w ((hasDerivAt_inv hn).differentiableAt.restrictScalars ℝ)).congr_of_eventuallyEq hw
  have hc := (spatial_equal_germ_end_coefficients he).1
  have hgc : immersionGaussMap Z =ᶠ[𝓝[≠] (0:ℂ)] fun w => Complex.exp (I*(α:ℂ)*w⁻¹+F w) := by
    filter_upwards [hc,tendsto_inv₀_nhdsNE_zero.eventually hg,hrc,self_mem_nhdsWithin] with w hw hg' hr hn
    change w ≠ 0 at hn
    change nullGauss (immersionComplexCoefficient Z w) = _
    rw [hw]
    have hswap : immersionGaussMap Y w = immersionGaussMap (X ∘ e.symm) w⁻¹ :=
      immersionGaussMap_comp_holomorphic hr (hasDerivAt_inv hn) (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hn)))
    simpa only [immersionGaussMap,inv_inv] using hswap.trans hg'
  filter_upwards [hy,punctured_germ_eventually_local hgc,hF.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with w hw he' ha hn
  change w ≠ 0 at hn
  have hg' := (((hasDerivAt_inv hn).differentiableAt.const_mul (I*(α:ℂ))).add ha.differentiableAt).cexp
  exact ⟨hw,hg'.congr_of_eventuallyEq he'⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compactified_exterior_end_regular
