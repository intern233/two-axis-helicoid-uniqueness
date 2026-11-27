import TwoAxisHelicoid.PlaneDerivativeOrientation
import TwoAxisHelicoid.ComplexEndCompactification

namespace TwoAxisHelicoid
open Complex Filter Set Topology
open scoped Topology ContDiff Manifold

variable {M : Type*} [TopologicalSpace M]

theorem planeChart_transition_source {e d : OpenPartialHomeomorph M ℂ} {x : M}
    (he : x ∈ e.source) (hd : x ∈ d.source) : e x ∈ (e.symm.trans d).source :=
  ⟨e.map_source he,by change e.symm (e x) ∈ d.source; rwa [e.left_inv he]⟩

noncomputable def planeChartIndex (e d : OpenPartialHomeomorph M ℂ) (x : M) : ℤ := by
  classical
  exact if h : x ∈ e.source ∧ x ∈ d.source then
    (openPartialHomeomorph_orientation_sign (e.symm.trans d) (planeChart_transition_source h.1 h.2)).choose else 1

theorem planeChartIndex_spec (e d : OpenPartialHomeomorph M ℂ) {x : M} (he : x ∈ e.source) (hd : x ∈ d.source) :
    (planeChartIndex e d x = 1 ∨ planeChartIndex e d x = -1) ∧
      HasPlaneOrientationAt (e.symm.trans d) (e x) (planeChartIndex e d x) := by
  unfold planeChartIndex
  split
  · exact (openPartialHomeomorph_orientation_sign (e.symm.trans d) (planeChart_transition_source he hd)).choose_spec
  · next h => exact (h ⟨he,hd⟩).elim

theorem planeChartIndex_comp (e d c : OpenPartialHomeomorph M ℂ) {x : M}
    (he : x ∈ e.source) (hd : x ∈ d.source) (hc : x ∈ c.source) :
    planeChartIndex e c x = planeChartIndex d c x * planeChartIndex e d x := by
  let f := e.symm.trans d
  let g := d.symm.trans c
  have hfx : f (e x) = d x := congrArg d (e.left_inv he)
  have h₁ := (planeChartIndex_spec e d he hd).2
  have h₂ : HasPlaneOrientationAt g (f (e x)) (planeChartIndex d c x) := hfx.symm ▸ (planeChartIndex_spec d c hd hc).2
  have htrans := openPartialHomeomorph_plane_orientation_comp f g (planeChart_transition_source he hd)
    (hfx.symm ▸ planeChart_transition_source hd hc) h₂ h₁
  have hsame : ⇑(e.symm.trans c) =ᶠ[𝓝 (e x)] g ∘ f := by
    filter_upwards [f.open_source.mem_nhds (planeChart_transition_source he hd)] with z hz
    exact congrArg c (d.left_inv hz.2).symm
  exact (planeChartIndex_spec e c he hc).2.unique (htrans.congr hsame)

theorem planeChartIndex_locally_constant (e d : OpenPartialHomeomorph M ℂ) {x : M}
    (he : x ∈ e.source) (hd : x ∈ d.source) :
    ∀ᶠ y in 𝓝 x, planeChartIndex e d y = planeChartIndex e d x := by
  have hsrc := planeChart_transition_source he hd
  have h := openPartialHomeomorph_orientation_locally_constant (e.symm.trans d) hsrc (planeChartIndex_spec e d he hd).2
  filter_upwards [e.open_source.mem_nhds he,d.open_source.mem_nhds hd,(e.continuousAt he).eventually h] with y h₁ h₂ hdeg
  exact (planeChartIndex_spec e d h₁ h₂).2.unique hdeg

/-- Two charts of any complex analytic reference atlas carry positive
local topological transition sign, even if it is unrelated as a
differentiable atlas to another structure on the surface. -/
theorem planeChartIndex_holomorphic [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {e d : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) {x : M} (hx : x ∈ e.source) (hy : x ∈ d.source) :
    planeChartIndex e d x = 1 := by
  let f := e.symm.trans d
  let z := e x
  have hsrc : z ∈ f.source := planeChart_transition_source hx hy
  have hfx : f z = d x := congrArg d (e.left_inv hx)
  have ha : AnalyticAt ℂ f z := (complexAtlas_realized_transition he hd hsrc).analyticAt
  have hb : AnalyticAt ℂ f.symm (f z) :=
    (complexAtlas_realized_transition hd he (hfx.symm ▸ planeChart_transition_source hy hx)).analyticAt
  have hsame : f.symm ∘ f =ᶠ[𝓝 z] id := by
    filter_upwards [f.open_source.mem_nhds hsrc] with w hw
    exact f.left_inv hw
  have hder := (deriv_comp z hb.differentiableAt ha.differentiableAt).symm.trans (hsame.deriv_eq.trans (deriv_id z))
  have hn : deriv f z ≠ 0 := fun h => by simp [h] at hder
  have hR := ha.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hpos : 0 < planeRealJacobian (fderiv ℝ f z) := by
    rw [hR.fderiv]
    change 0 < (1*deriv f z).re*(I*deriv f z).im-(1*deriv f z).im*(I*deriv f z).re
    have hs := Complex.normSq_pos.mpr hn
    simp only [one_mul,Complex.I_mul_re,Complex.I_mul_im,Complex.normSq_apply] at *
    linarith
  have hc : ∀ᶠ w in 𝓝 z, ContinuousAt f w := (show ∀ᶠ w in 𝓝 z, w ∈ f.source from
    f.open_source.mem_nhds hsrc).mono fun _ hw => f.continuousAt hw
  exact (planeChartIndex_spec e d hx hy).2.unique
    (hasFDerivAt_positive_local_orientation (ha.differentiableAt.restrictScalars ℝ).hasFDerivAt hc hpos)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.planeChartIndex_holomorphic
