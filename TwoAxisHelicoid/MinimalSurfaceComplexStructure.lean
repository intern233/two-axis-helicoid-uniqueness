import TwoAxisHelicoid.IsothermalChartOrientation

namespace TwoAxisHelicoid
open Complex Matrix Filter Set InnerProductSpace
open scoped Topology ContDiff Manifold ComplexConjugate
set_option maxHeartbeats 1500000

variable {M : Type*} [TopologicalSpace M]

/-- A regular minimal patch with a transverse ambient orientation field
can itself be replaced by a genuine oriented isothermal immersion chart. -/
theorem minimal_patch_oriented_isothermal {F N : M → Fin 3 → ℝ} (hN : Continuous N)
    {e : OpenPartialHomeomorph M ℂ} {x : M} (hx : x ∈ e.source)
    (hX : ContDiffAt ℝ 2 (F ∘ e.symm) (e x)) (hi : Function.Injective (fderiv ℝ (F ∘ e.symm) (e x)))
    (hm : ∀ᶠ y in 𝓝 (e x), coordinateMeanCurvature (F ∘ e.symm) y = 0)
    (ho : surfaceTangentCross (F ∘ e.symm) (e x) ⬝ᵥ N x ≠ 0) :
    ∃ d : OpenPartialHomeomorph M ℂ, OrientedIsothermalChart F N d ∧ x ∈ d.source := by
  let X := F ∘ e.symm
  let z := e x
  obtain ⟨k,hz,_,hks,hfactor,hhar,_⟩ := regular_minimal_chart_actual_complex_data hX hi hm
  let a := e.trans k
  let w := a x
  let Y := F ∘ a.symm
  have hw : x ∈ a.source := ⟨hx,hz⟩
  have hw' : w ∈ a.target := a.map_source hw
  have hY : HarmonicAt Y w := hhar
  have hf : ∀ᶠ y in 𝓝 w, ∃ c : ℝ, 0 < c ∧ ∀ v,
      fderiv ℝ Y y v ⬝ᵥ fderiv ℝ Y y v = c*normSq v := hfactor
  let φ := fun y => surfaceTangentCross Y y ⬝ᵥ N (a.symm y)
  have hc : ContinuousAt φ w := continuousAt_surfaceTransversal hw' hN hY.1
  have hφ : φ w ≠ 0 := by
    have hX' : DifferentiableAt ℝ X (k.symm w) := by
      change DifferentiableAt ℝ X (k.symm (k z))
      rw [k.left_inv hz]
      exact hX.differentiableAt two_ne_zero
    have hcross := surfaceTangentCross_coordinate_change (X := Y) (Y := X) (f := k.symm) (z := w)
      Filter.EventuallyEq.rfl hX' (hks.differentiableAt two_ne_zero)
    let d := planeRealJacobian (fderiv ℝ k.symm w)
    change surfaceTangentCross Y w = d • surfaceTangentCross X (k.symm (k z)) at hcross
    rw [k.left_inv hz] at hcross
    obtain ⟨c,hc',hg⟩ := hf.self_of_nhds
    have hd : d ≠ 0 := by
      intro hh
      rw [hh,zero_smul] at hcross
      exact surfaceTangentCross_nonzero_of_factor hc' hg hcross
    change surfaceTangentCross Y w ⬝ᵥ N (a.symm (a x)) ≠ 0
    rw [a.left_inv hw,hcross,smul_dotProduct,smul_eq_mul]
    exact mul_ne_zero hd ho
  have hsign : ∀ᶠ y in 𝓝 w, 0 < φ y * φ w := by
    exact (hc.mul continuousAt_const).eventually (Ioi_mem_nhds (mul_self_pos.mpr hφ))
  have hg : ∀ᶠ y in 𝓝 w,
      (ContDiffAt ℝ ∞ Y y ∧ Function.Injective (fderiv ℝ Y y)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ v, fderiv ℝ Y y v ⬝ᵥ fderiv ℝ Y y v = c*normSq v) ∧
      0 < φ y * φ w := by
    filter_upwards [hf,(isOpen_setOfPred_harmonicAt Y).mem_nhds hY,hsign] with y hh hy hs
    obtain ⟨c,hc',hmc⟩ := hh
    exact ⟨⟨harmonic_surface_param_smooth hy,(conformal_immersion_of_metric_factor _ hc' hmc).2.2⟩,
      ⟨c,hc',hmc⟩,hs⟩
  obtain ⟨U,hU,hopen,hwU⟩ := mem_nhds_iff.mp hg
  let d := a.trans (OpenPartialHomeomorph.ofSet U hopen)
  have hdx : x ∈ d.source := ⟨hw,hwU⟩
  have hreg : RegularImmersionChart F d := fun y hy => (hU hy.1).1
  have hmet (y : ℂ) (hy : y ∈ d.target) : ∃ c : ℝ, 0 < c ∧ ∀ v,
      fderiv ℝ (F ∘ d.symm) y v ⬝ᵥ fderiv ℝ (F ∘ d.symm) y v = c*normSq v := (hU hy.1).2.1
  by_cases hp : 0 < φ w
  · refine ⟨d,⟨hreg,?_⟩,hdx⟩
    intro y hy
    exact ⟨hmet y hy,pos_of_mul_pos_left (hU hy.1).2.2 hp.le⟩
  · refine ⟨d.trans conjCLE.toHomeomorph.toOpenPartialHomeomorph,
      isothermal_chart_reverse hreg hmet ?_,hdx,mem_univ _⟩
    intro y hy
    rcases mul_pos_iff.mp (hU hy.1).2.2 with h | h
    · exact (hp h.2).elim
    · exact h.1

/-- Standard complex analytic manifold structure induced by an arbitrary
cooriented C² minimal immersion. The input charts are real with vanishing
geometric mean curvature. The conformal charts are constructed. -/
theorem minimal_surface_induced_complex_structure {F N : M → Fin 3 → ℝ} (hN : Continuous N)
    (hcover : ∀ x : M, ∃ e : OpenPartialHomeomorph M ℂ, x ∈ e.source ∧
      ContDiffAt ℝ 2 (F ∘ e.symm) (e x) ∧ Function.Injective (fderiv ℝ (F ∘ e.symm) (e x)) ∧
      (∀ᶠ y in 𝓝 (e x), coordinateMeanCurvature (F ∘ e.symm) y = 0) ∧
      surfaceTangentCross (F ∘ e.symm) (e x) ⬝ᵥ N x ≠ 0) :
    ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ ∀ e ∈ atlas ℂ M, OrientedIsothermalChart F N e := by
  have hc (x : M) : ∃ d : OpenPartialHomeomorph M ℂ, OrientedIsothermalChart F N d ∧ x ∈ d.source := by
    obtain ⟨e,hx,hX,hi,hm,ho⟩ := hcover x
    exact minimal_patch_oriented_isothermal hN hx hX hi hm ho
  exact ⟨isothermalComplexAtlas F N hc,isothermalComplexAtlas_isManifold F N hc,fun _ he => he⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.minimal_surface_induced_complex_structure
