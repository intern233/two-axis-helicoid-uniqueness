import TwoAxisHelicoid.PlaneAffineGradientStability

namespace TwoAxisHelicoid
open MeasureTheory Complex Set Filter InnerProductSpace
open scoped ContDiff RealInnerProductSpace

/-- Solve a coercive variational equation with an arbitrary L² load on a
closed Hilbert subspace, and return the actual bounded inverse on that subspace. -/
theorem exists_restricted_flux_inverse {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (S : Submodule ℝ E) (closed : IsClosed (S:Set E))
    (T : E →L[ℝ] E) {c : ℝ} (hc : 0<c) (lower : ∀ v, c*‖v‖^2≤⟪T v,v⟫_ℝ) :
    ∃ B : S ≃L[ℝ] S, ∀ u v : S, ⟪B u,v⟫_ℝ=⟪T (u:E),(v:E)⟫_ℝ := by
  let : CompleteSpace S := closed.completeSpace_coe
  let inc := S.subtypeL
  let Q : S →L[ℝ] S →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ S E ℝ).flip inc).comp ((innerSL ℝ).comp (T.comp inc))
  have co : IsCoercive Q := by
    refine ⟨c,hc,fun v => ?_⟩
    change c*‖v‖*‖v‖≤⟪T (v:E),(v:E)⟫_ℝ
    simpa only [pow_two,mul_assoc,Submodule.norm_coe] using lower (v:E)
  exact ⟨co.continuousLinearEquivOfBilin,co.continuousLinearEquivOfBilin_apply⟩

theorem coercive_flux_unique_load {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (S : Submodule ℝ E) (closed : IsClosed (S:Set E)) (T : E →L[ℝ] E)
    {c : ℝ} (hc : 0<c) (lower : ∀ v, c*‖v‖^2≤⟪T v,v⟫_ℝ) (load : E) :
    ∃! u : S, ∀ v : S, ⟪T (u:E)-load,(v:E)⟫_ℝ=0 := by
  let : CompleteSpace S := closed.completeSpace_coe
  obtain ⟨B,eval⟩ := exists_restricted_flux_inverse S closed T hc lower
  let rhs : S →L[ℝ] ℝ := (innerSL ℝ load).comp S.subtypeL
  let z := (InnerProductSpace.toDual ℝ S).symm rhs
  have pairing (v : S) : ⟪z,v⟫_ℝ=⟪load,(v:E)⟫_ℝ :=
    InnerProductSpace.toDual_symm_apply
  refine ⟨B.symm z,?_,?_⟩
  · intro v
    rw [inner_sub_left,←eval,B.apply_symm_apply,pairing,sub_self]
  · intro w hw
    apply B.injective
    rw [B.apply_symm_apply]
    apply ext_inner_right ℝ
    intro v
    have eq := hw v
    rw [inner_sub_left,←eval,←pairing] at eq
    exact sub_eq_zero.mp eq

noncomputable def planeAffineFluxLoad (A B C : ℂ → ℝ) (z : ℂ) : ℂ :=
  1-planeMetricFlux A B C z 1

theorem planeAffineFluxLoad_continuous {A B C : ℂ → ℝ} (sa : Continuous A)
    (sb : Continuous B) (sc : Continuous C) : Continuous (planeAffineFluxLoad A B C) := by
  apply continuous_const.sub
  change Continuous (Complex.equivRealProdCLM.symm ∘ (fun z : ℂ =>
    (C z*(1:ℂ).re-B z*(1:ℂ).im,A z*(1:ℂ).im-B z*(1:ℂ).re)))
  apply Complex.equivRealProdCLM.symm.continuous.comp
  apply Continuous.prodMk <;> fun_prop (disch := assumption)

theorem planeAffineFluxLoad_compact {A B C : ℂ → ℝ}
    {K : Set ℂ} (hk : IsCompact K) (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1) :
    HasCompactSupport (planeAffineFluxLoad A B C) := by
  apply HasCompactSupport.of_support_subset_isCompact hk
  intro z hz
  by_contra h
  obtain ⟨a,b,c⟩ := off z h
  apply hz
  apply Complex.ext <;> simp [planeAffineFluxLoad,planeMetricFlux,a,b,c]

/-- On the full plane the affine background need not be in L². Subtracting
its constant Euclidean flux instead gives a compactly supported actual load.
The finite-energy gradient correction exists uniquely. -/
theorem exists_whole_plane_affine_corrector {A B C : ℂ → ℝ}
    (sa : Continuous A) (sb : Continuous B) (sc : Continuous C) (ha : ∀ z, 0<A z)
    (det : ∀ z, A z*C z-(B z)^2=1) {K : Set ℂ} (hk : IsCompact K)
    (off : ∀ z∉K, A z=1 ∧ B z=0 ∧ C z=1) :
    ∃ (k : ℝ) (T : Lp ℂ 2 (volume:Measure ℂ) →L[ℝ] Lp ℂ 2 (volume:Measure ℂ))
      (b : Lp ℂ 2 (volume:Measure ℂ)), 1≤k ∧
      (∀ w, ⇑(T w) =ᵐ[volume] (fun z => planeMetricFlux A B C z (w z))) ∧
      (∀ w, k⁻¹*‖w‖^2≤⟪T w,w⟫_ℝ) ∧ (⇑b =ᵐ[volume] planeAffineFluxLoad A B C) ∧
      ∃! u : planeDirichletGradients volume univ,
        ∀ v : planeDirichletGradients volume univ, ⟪T u.val-b,v.val⟫_ℝ=0 := by
  obtain ⟨k,T,hk1,acts,lower⟩ := compact_conductivity_operator_coercive volume sa sb sc ha det hk off
  let m := (planeAffineFluxLoad_continuous sa sb sc).memLp_of_hasCompactSupport
    (μ:=volume) (p:=2) (planeAffineFluxLoad_compact hk off)
  let b := m.toLp _
  have kp : 0<k := by linarith
  refine ⟨k,T,b,hk1,acts,lower,m.coeFn_toLp,?_⟩
  exact coercive_flux_unique_load _ (Submodule.isClosed_topologicalClosure _) T (inv_pos.mpr kp) lower b

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_restricted_flux_inverse
#print axioms TwoAxisHelicoid.exists_whole_plane_affine_corrector
