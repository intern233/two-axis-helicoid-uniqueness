import TwoAxisHelicoid.PuncturedMarkedTangentFrame
import TwoAxisHelicoid.RegularTorusFrameCurves

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Along a regular homotopy the lift test for an actual marked
generator is constant. Only the real differential of the spatial map
on this generator and its joint continuity are used. -/
theorem torus_generator_closed_of_regular_homotopy (L : PeriodPair)
    (F : unitInterval → PeriodTorus L → Fin 3 → ℝ) (i : Fin 2)
    (hc : Continuous (fun w : unitInterval × unitInterval =>
      fderiv ℝ (F w.1 ∘ periodTorusProjection L) (periodBasisLine L i w.2.1)))
    (hi : ∀ w : unitInterval × unitInterval, Function.Injective
      (fderiv ℝ (F w.1 ∘ periodTorusProjection L) (periodBasisLine L i w.2.1)))
    (h0 : CapGeneratorAmbientSpinCloses L (F 0) i) : CapGeneratorAmbientSpinCloses L (F 1) i := by
  let D (w : unitInterval × unitInterval) := fderiv ℝ (F w.1 ∘ periodTorusProjection L) (periodBasisLine L i w.2.1)
  let H : C(unitInterval × unitInterval,OrthonormalTangentPair) := ⟨fun w => spatialDifferentialFrame (hi w) (L.basis.ne_zero i),
    spatialDifferentialFrame_continuous hc continuous_const hi (fun _ => L.basis.ne_zero i)⟩
  have he (s : unitInterval) : H (s,1) = H (s,0) := by
    have hh : D (s,1) = D (s,0) := by
      change fderiv ℝ _ (periodBasisLine L i 1) = fderiv ℝ _ (periodBasisLine L i 0)
      rw [show periodBasisLine L i 1 = periodBasisLine L i 0+L.basis i by simpa only [zero_add] using periodBasisLine_add_one L i 0]
      exact lifted_fderiv_periodic L (F s) _ _ ((periodGeneratorPeriod_val L i) ▸ (periodGeneratorPeriod L i).2)
    apply Subtype.ext
    change spatialGramFrame (D (s,1) _) (D (s,1) _) = spatialGramFrame (D (s,0) _) (D (s,0) _)
    rw [hh]
  obtain ⟨a,ha,haf⟩ := h0
  obtain ⟨b,hb,hbe⟩ := quaternion_loop_closed_lift_homotopy H he a (fun t => Subtype.ext (haf t)) ha
  exact ⟨b,hbe,fun t => congrArg Subtype.val (hb t)⟩

/-- The spin Arf invariant of the initial surface is even if the actual
terminal surface has even Arf. No marked-coordinate preservation is
required of a terminal parametrization. -/
theorem marked_arf_even_of_regular_homotopy (L : PeriodPair)
    (F : unitInterval → PeriodTorus L → Fin 3 → ℝ)
    (hc : ∀ i : Fin 2, Continuous (fun w : unitInterval × unitInterval =>
      fderiv ℝ (F w.1 ∘ periodTorusProjection L) (periodBasisLine L i w.2.1)))
    (hi : ∀ (i : Fin 2) (w : unitInterval × unitInterval), Function.Injective
      (fderiv ℝ (F w.1 ∘ periodTorusProjection L) (periodBasisLine L i w.2.1)))
    (ht : capAmbientSpinQuadratic L (F 1) (1,0) * capAmbientSpinQuadratic L (F 1) (0,1) = 0) :
    capAmbientSpinQuadratic L (F 0) (1,0) * capAmbientSpinQuadratic L (F 0) (0,1) = 0 := by
  classical
  by_cases h0 : CapGeneratorAmbientSpinCloses L (F 0) 0
  · by_cases h1 : CapGeneratorAmbientSpinCloses L (F 0) 1
    · have he0 := torus_generator_closed_of_regular_homotopy L F 0 (hc 0) (hi 0) h0
      have he1 := torus_generator_closed_of_regular_homotopy L F 1 (hc 1) (hi 1) h1
      simp [capAmbientSpinQuadratic,torusQuadratic,he0,he1] at ht
    · simp [capAmbientSpinQuadratic,torusQuadratic,h0,h1]
  · simp [capAmbientSpinQuadratic,torusQuadratic,h0]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_arf_even_of_regular_homotopy
