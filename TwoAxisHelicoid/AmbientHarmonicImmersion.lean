import TwoAxisHelicoid.MinimalChartComplexData
import TwoAxisHelicoid.AlignedEndDoublePoles

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology InnerProductSpace
open scoped Topology Laplacian

/-- A Euclidean spatial map with three harmonic component functions is
itself a vector-valued harmonic map. -/
theorem spatial_harmonic_of_coordinates {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hh : ∀ j, HarmonicAt (fun w => X w j) z) : HarmonicAt X z := by
  have hX : ContDiffAt ℝ 2 X z := contDiffAt_pi.mpr (fun j => (hh j).1)
  refine ⟨hX,?_⟩
  have he (j : Fin 3) : ∀ᶠ w in 𝓝 z, (Δ X) w j = 0 := by
    let l : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
    filter_upwards [hX.laplacian_CLM_comp_left_nhds (l := l),(hh j).2] with w hw h0
    exact hw.symm.trans h0
  filter_upwards [eventually_all.mpr he] with w hw
  exact funext hw

/-- A genuine ambient Euclidean isometry preserves harmonicity,
conformality and regularity of the original three coordinate functions. -/
theorem orthogonal_affine_harmonic_immersion
    (L : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (hL : ∀ a b, L a ⬝ᵥ L b = a ⬝ᵥ b) (P : Fin 3 → ℝ)
    {X : ℂ → Fin 3 → ℝ} {z : ℂ} (hh : ∀ j, HarmonicAt (fun w => X w j) z)
    (hc : ConformalCoordinateDerivatives X z) (hr : Function.Injective (fderiv ℝ X z)) :
    let Y := fun w => P+L (X w)
    (∀ j, HarmonicAt (fun w => Y w j) z) ∧ ConformalCoordinateDerivatives Y z ∧
      Function.Injective (fderiv ℝ Y z) := by
  let T := L.toContinuousLinearEquiv
  let Y := fun w => P+L (X w)
  have hhX := spatial_harmonic_of_coordinates hh
  have hhY : HarmonicAt Y z := (harmonicAt_const P).add (hhX.comp_CLM T.toContinuousLinearMap)
  have hXD := hhX.1.differentiableAt two_ne_zero
  have hD : HasFDerivAt Y (T.toContinuousLinearMap.comp (fderiv ℝ X z)) z :=
    (T.toContinuousLinearMap.hasFDerivAt.comp z hXD.hasFDerivAt).const_add P
  have hdot := (conformalCoordinateDerivatives_iff_dot hXD).mp hc
  refine ⟨fun j => hhY.comp_CLM (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ),?_,?_⟩
  · apply (conformalCoordinateDerivatives_iff_dot hD.differentiableAt).mpr
    rw [hD.fderiv]
    change L _ ⬝ᵥ L _ = L _ ⬝ᵥ L _ ∧ L _ ⬝ᵥ L _ = 0
    rw [hL,hL,hL]
    exact hdot
  · rw [hD.fderiv]
    exact L.injective.comp hr

theorem marked_harmonic_end_null {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X w j) z) ∧
      ConformalCoordinateDerivatives X z ∧ Function.Injective (fderiv ℝ X z)) :
    ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ X w ∧ ComplexNull (immersionComplexCoefficient X w) ∧
      ∀ j, AnalyticAt ℂ (fun y => immersionComplexCoefficient X y j) w := by
  filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),self_mem_nhdsWithin] with w hw hn
  have hwl : w ∉ L.lattice := fun hh => hw ⟨hh,hn⟩
  obtain ⟨hh,hc,_⟩ := hhi _ hwl
  exact ⟨(spatial_harmonic_of_coordinates hh).1.differentiableAt two_ne_zero,immersionComplexCoefficient_null hc,
    fun j => scalarComplexCoefficient_analyticAt (hh j)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.orthogonal_affine_harmonic_immersion
