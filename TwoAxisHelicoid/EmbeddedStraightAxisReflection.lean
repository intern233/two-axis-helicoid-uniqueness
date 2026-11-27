import TwoAxisHelicoid.AnalyticEmbeddedDefiningEquation
import TwoAxisHelicoid.StraightAxisLocalSymmetry
import TwoAxisHelicoid.HarmonicComplexCoefficient

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology InnerProductSpace
open scoped Topology ComplexConjugate

/-- For an embedded harmonic conformal chart, inclusion of a spatial straight
line supplies its regular parameter and an actual anti-holomorphic reflection
germ, both within the same surface. -/
theorem embedded_axis_local_reflection {M : Type*} [TopologicalSpace M]
    {X : M → Fin 3 → ℝ} (hX : IsEmbedding X) (e : OpenPartialHomeomorph M ℂ)
    {p : M} (hp : p ∈ e.source) (hzero : X p = 0)
    (haxis : ∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ) ∈ range X)
    (hY : AnalyticAt ℝ (X ∘ e.symm) (e p))
    (hi : Function.Injective (fderiv ℝ (X ∘ e.symm) (e p)))
    (hh : ∀ᶠ w in 𝓝 (e p), (∀ j, HarmonicAt (fun u => X (e.symm u) j) w) ∧
      ConformalCoordinateDerivatives (X ∘ e.symm) w) :
    ∃ S : ℂ → ℂ, AnalyticAt ℂ S (conj (e p)) ∧ S (conj (e p)) = e p ∧
      ∀ᶠ w in 𝓝 (e p), S (conj w) ∈ e.target ∧ X (e.symm (S (conj w))) = halfTurnX (X (e.symm w)) := by
  let Y := X ∘ e.symm
  obtain ⟨τ,hτ,hτ0,hnear⟩ := embedded_surface_local_analytic_inverse hX e hp hY hi
  let A := fun s : ℝ => (![s,0,0] : Fin 3 → ℝ)
  have hA : AnalyticAt ℝ A 0 := by
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases j
    · exact analyticAt_id
    · exact analyticAt_const
    · exact analyticAt_const
  have hA0 : A 0 = X p := by
    rw [hzero]
    ext j
    fin_cases j <;> rfl
  have ht : Tendsto A (𝓝 0) (𝓝[range X] (X p)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hA0 ▸ hA.continuousAt.tendsto,Eventually.of_forall haxis⟩
  let σ := τ ∘ A
  have hσ : AnalyticAt ℝ σ 0 := (show AnalyticAt ℝ τ (A 0) by rwa [hA0]).comp hA
  have heq : σ 0 = e p := by change τ (A 0) = _; rw [hA0,hτ0]
  have hv : ∀ᶠ s in 𝓝 (0:ℝ), Y (σ s) = A s := ht.eventually hnear
  have hYnear := (isOpen_analyticAt ℝ Y).mem_nhds hY
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp ((hh.and hYnear).and (e.open_target.mem_nhds (e.map_source hp)))
  have hb : ∀ᶠ s in 𝓝 (0:ℝ), σ s ∈ ball (e p) R := by
    apply hσ.continuousAt.eventually
    rw [heq]
    exact ball_mem_nhds _ hR
  obtain ⟨r,hr,hI⟩ := Metric.mem_nhds_iff.mp ((hv.and hb).and ((isOpen_analyticAt ℝ σ).mem_nhds hσ))
  rw [Real.ball_eq_Ioo,zero_sub,zero_add] at hI
  rw [← heq] at hball
  let Φ := immersionComplexCoefficient Y
  obtain ⟨W,hW,hWs,hne,hXW⟩ := straight_axis_exists_holomorphic_coordinate
    (X := Y) (Φ := Φ) (σ := σ) (v := deriv σ) hr hR
    (fun w hw => scalarComplexCoefficient_analyticAt ((hball hw).1.1.1 0))
    (fun w hw => immersionComplexCoefficient_null (hball hw).1.1.2)
    (fun w hw => immersionComplexCoefficient_hasFDerivAt (hball hw).1.2.differentiableAt)
    (fun s hs => (hI hs).2.differentiableAt.hasDerivAt)
    (fun s hs => heq.symm ▸ (hI hs).1.2) (fun s hs => (hI hs).1.1)
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨neg_lt_zero.mpr hr,hr⟩
  have hW0 : W (σ 0) = 0 := by simpa using hWs _ h0
  have hWa : AnalyticAt ℂ W (σ 0) :=
    (DifferentiableOn.analyticOnNhd (fun w hw => (hW w hw).differentiableAt.differentiableWithinAt) isOpen_ball) _ (mem_ball_self hR)
  obtain ⟨S,hS,hs0,hrel⟩ := straightened_harmonic_surface_local_half_turn hR
    (fun j w hw => (hball hw).1.1.1 j) hWa hW0 hne hXW hσ.continuousAt
    (show ∀ᶠ s in 𝓝 (0:ℝ), W (σ s) = (s:ℂ) ∧ Y (σ s) = ![s,0,0] from
      (show ∀ᶠ s in 𝓝 (0:ℝ), s ∈ Ioo (-r) r from isOpen_Ioo.mem_nhds h0).mono (fun s hs => ⟨hWs s hs,(hI hs).1.1⟩))
  rw [← heq]
  exact ⟨S,hS,hs0,hrel.mono fun w hw => ⟨(hball hw.1).2,hw.2⟩⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.embedded_axis_local_reflection
