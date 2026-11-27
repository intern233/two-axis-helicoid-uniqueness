import TwoAxisHelicoid.WeierstrassUnitSegments
import TwoAxisHelicoid.ThinCurveProjection

namespace TwoAxisHelicoid
open Complex Real Set
set_option maxHeartbeats 1000000

noncomputable def coordinateToTube : (Fin 3 → ℝ) →L[ℝ] HelicoidTubeCoordinates :=
  ((ContinuousLinearMap.proj (0 : Fin 3)).prod (ContinuousLinearMap.proj (1 : Fin 3))).prod
    (ContinuousLinearMap.proj (2 : Fin 3))

@[simp] theorem tubeCartesian_coordinateToTube (v : Fin 3 → ℝ) :
    tubeCartesian (coordinateToTube v) = v := by
  funext j
  fin_cases j <;> rfl

/-- On an actual holomorphic Weierstrass end, bounded derivative of log g
and arbitrary thin tails produce the controlled curves. The curves and
their acceleration estimates are proved, not supplied as hypotheses. -/
theorem holomorphic_thin_end_controlled_tangent_curves
    {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hW : ∀ z : ℂ, R < ‖z‖ → AnalyticAt ℂ W z)
    (hbound : ∀ z : ℂ, R < ‖z‖ → ‖deriv W z‖ ≤ L)
    (hX : ∀ z : ℂ, R < ‖z‖ →
      HasFDerivAt X (nullRealDerivative (weierstrassTriple (exp (W z)) 1)) z)
    (hthin : ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, ∀ z : ℂ, S < ‖z‖ →
      coordinateToTube (X z) ∈ helicoidTubeEquiv.target ∧
      |helicoidSignedDistance (coordinateToTube (X z))| ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ∃ T : ℝ, 0 < T ∧ ∀ z : ℂ, T < ‖z‖ →
      HasControlledUnitTangentCurves (coordinateToTube (X z))
        (coordinateToTube.comp (nullRealDerivative (weierstrassTriple (exp (W z)) 1))) ε L := by
  intro ε hε0 hε
  obtain ⟨S,hS⟩ := hthin ε hε0
  let B := max R (max S 1)
  have hRB : R ≤ B := le_max_left _ _
  have hSB : S ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hB : 0 ≤ B := hR.trans hRB
  refine ⟨B+4,by positivity,?_⟩
  intro z₀ hz₀ v₀ hv₀
  have hunit : (∑ j, (nullRealDerivative (weierstrassTriple (exp (W z₀)) 1) v₀ j)^2) = 1 := by
    simpa only [ContinuousLinearMap.comp_apply,tubeCartesian_coordinateToTube] using hv₀
  obtain ⟨γ,w,a,hγ0,hw0,hseg⟩ := holomorphic_height_end_actual_unit_segments hB hL
    (fun z hz => hW z (hRB.trans_lt hz)) (fun z hz => hbound z (hRB.trans_lt hz))
    (fun z hz => hX z (hRB.trans_lt hz)) z₀ v₀ hz₀ hunit
  have hroot : sqrt ε ≤ 1 := by nlinarith [sq_sqrt hε0.le,sqrt_nonneg ε]
  have hsub : Icc (0 : ℝ) (sqrt ε) ⊆ Icc 0 1 :=
    fun _ ht => ⟨ht.1,ht.2.trans hroot⟩
  have hthinγ t (ht : t ∈ Icc (0 : ℝ) 1) :
      coordinateToTube (X (γ t)) ∈ helicoidTubeEquiv.target ∧
      |helicoidSignedDistance (coordinateToTube (X (γ t)))| ≤ ε :=
    hS (γ t) (by linarith [(hseg t ht).1])
  refine ⟨coordinateToTube ∘ X ∘ γ,coordinateToTube ∘ w,coordinateToTube ∘ a,
    by simp only [Function.comp_apply,hγ0],
    by simp only [Function.comp_apply,hw0,ContinuousLinearMap.comp_apply],?_,?_,?_,?_,?_,?_⟩
  · intro t ht
    exact coordinateToTube.hasFDerivAt.comp_hasDerivAt t (hseg t (hsub ht)).2.1
  · intro t ht
    exact coordinateToTube.hasFDerivAt.comp_hasDerivAt t (hseg t (hsub ht)).2.2.1
  · intro t ht
    exact (hthinγ t (hsub ht)).1
  · intro t ht
    exact (hthinγ t (hsub ht)).2
  · intro t ht
    simpa only [Function.comp_apply,tubeCartesian_coordinateToTube] using
      (hseg t (hsub ht)).2.2.2.1.le
  · intro t ht
    simpa only [Function.comp_apply,tubeCartesian_coordinateToTube] using
      (hseg t (hsub ht)).2.2.2.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.holomorphic_thin_end_controlled_tangent_curves
