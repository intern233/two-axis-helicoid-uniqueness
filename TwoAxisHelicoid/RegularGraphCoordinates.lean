import TwoAxisHelicoid.MinimalGraphIsothermal

namespace TwoAxisHelicoid
open Complex Set Filter Matrix
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- Projection to two ambient coordinate directions, identified with the
ordinary complex plane only as a real coordinate space. -/
noncomputable def spatialGraphProjection (i j : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℂ :=
  equivRealProdCLM.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.proj i).prod (ContinuousLinearMap.proj j))

/-- A regular tangent plane admits a nondegenerate coordinate minor.
No graph directions are supplied as hypotheses. -/
theorem regular_immersion_coordinate_minor (D : ℂ →L[ℝ] (Fin 3 → ℝ))
    (hi : Function.Injective D) :
    ∃ i j : Fin 3, i ≠ j ∧ D 1 i*D I j - D 1 j*D I i ≠ 0 := by
  by_contra he
  push Not at he
  have ha : D 1 ≠ 0 := fun h => one_ne_zero (hi (h.trans D.map_zero.symm))
  obtain ⟨i,hi'⟩ : ∃ i, D 1 i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact ha (funext hn)
  let r := D I i/D 1 i
  have hr (j : Fin 3) : D I j = r * D 1 j := by
    by_cases hj : i=j
    · subst j
      dsimp [r]
      field_simp
    · have h := he i j hj
      dsimp [r]
      field_simp
      linear_combination h
  have hz : D I = D (r • (1:ℂ)) := by
    rw [map_smul]
    exact funext hr
  have hh := congrArg Complex.im (hi hz)
  simp [Complex.real_smul] at hh

theorem spatialGraphProjection_injective (D : ℂ →L[ℝ] (Fin 3 → ℝ))
    (i j : Fin 3) (hm : D 1 i*D I j-D 1 j*D I i ≠ 0) :
    Function.Injective ((spatialGraphProjection i j).comp D) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have h0 : D v i = 0 := congrArg Complex.re hv
  have h1 : D v j = 0 := congrArg Complex.im hv
  rw [real_linear_complex_expansion D v] at h0 h1
  change v.re * D 1 i + v.im * D I i = 0 at h0
  change v.re * D 1 j + v.im * D I j = 0 at h1
  have hr : v.re*(D 1 i*D I j-D 1 j*D I i) = 0 := by
    linear_combination D I j * h0 - D I i * h1
  have him : v.im*(D 1 i*D I j-D 1 j*D I i) = 0 := by
    linear_combination D 1 i * h1 - D 1 j * h0
  exact Complex.ext ((mul_eq_zero.mp hr).resolve_right hm) ((mul_eq_zero.mp him).resolve_right hm)

/-- Each regular real parametrization admits a local graph chart over an
actual pair of Cartesian coordinates. The remaining coordinate is then
a height function on the projection. -/
theorem regular_immersion_graph_chart {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X z) (hi : Function.Injective (fderiv ℝ X z)) :
    ∃ (σ : Equiv.Perm (Fin 3)) (e : OpenPartialHomeomorph ℂ ℂ) (u : ℂ → ℝ),
      z ∈ e.source ∧ ContDiffAt ℝ 2 e z ∧ ContDiffAt ℝ 2 e.symm (e z) ∧
      ContDiffAt ℝ 2 u (e z) ∧
      ∀ w ∈ e.target, (X (e.symm w) (σ 0), X (e.symm w) (σ 1), X (e.symm w) (σ 2)) =
        (w.re,w.im,u w) := by
  obtain ⟨i,j,hij,hm⟩ := regular_immersion_coordinate_minor _ hi
  have hperm : ∀ i j : Fin 3, i ≠ j → ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j := by decide
  obtain ⟨σ,h0,h1⟩ := hperm i j hij
  let P := spatialGraphProjection i j
  let f := P ∘ X
  let D := P.comp (fderiv ℝ X z)
  have hf : ContDiffAt ℝ 2 f z := P.contDiff.contDiffAt.comp z hX
  have hD : HasFDerivAt f D z := P.hasFDerivAt.comp z (hX.differentiableAt two_ne_zero).hasFDerivAt
  have hiD : Function.Injective D := spatialGraphProjection_injective _ _ _ hm
  let D' := (LinearEquiv.ofBijective D.toLinearMap ⟨hiD,LinearMap.injective_iff_surjective.mp hiD⟩).toContinuousLinearEquiv
  have hD' : HasFDerivAt f (D' : ℂ →L[ℝ] ℂ) z := hD
  let e := hf.toOpenPartialHomeomorph f hD' two_ne_zero
  have hez : z ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hD' two_ne_zero
  have hes : ContDiffAt ℝ 2 e.symm (e z) := hf.to_localInverse hD' two_ne_zero
  let u := fun w => X (e.symm w) (σ 2)
  refine ⟨σ,e,u,hez,hf,hes,?_,?_⟩
  · have hx : ContDiffAt ℝ 2 X (e.symm (e z)) := (e.left_inv hez).symm ▸ hX
    exact (ContinuousLinearMap.proj (σ 2) : (Fin 3 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt.comp _ (hx.comp _ hes)
  · intro w hw
    have he : spatialGraphProjection i j (X (e.symm w)) = w := e.right_inv hw
    rw [h0,h1]
    have hr := congrArg Complex.re he
    have hI := congrArg Complex.im he
    exact Prod.ext hr (Prod.ext hI rfl)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_immersion_graph_chart
