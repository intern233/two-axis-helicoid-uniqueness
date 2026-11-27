import TwoAxisHelicoid.RegularTorusFrameCurves

namespace TwoAxisHelicoid
open Complex Set

/-- For a regular parametrization on the standard marked torus, closure on
both standard generators forces closure of the actual tangent-adapted
ambient frame of every regular simple essential curve. -/
theorem torus_ambient_lifts_along_essential_curve (L : PeriodPair) {F : PeriodTorus L → Fin 3 → ℝ}
    (hD : Continuous (fderiv ℝ (F ∘ periodTorusProjection L)))
    (hi : ∀ z, Function.Injective (fderiv ℝ (F ∘ periodTorusProjection L) z))
    (hgen : ∀ i, CapGeneratorAmbientSpinCloses L F i)
    {ξ : ℝ → ℂ} (hξ : ContDiff ℝ 1 ξ) {ω : ℂ} (hω : ω ≠ 0) (hωL : ω ∈ L.lattice)
    (hp : ∀ t, ξ (t+1) = ξ t+ω) (hr : ∀ t, deriv ξ t ≠ 0)
    (hinj : ∀ t h : ℝ, h ∈ Ioo (0:ℝ) 1 → ξ (t+h) ≠ ξ t) :
    SpatialFrameCurveCloses (fun t => spatialDifferentialFrame (hi (ξ t.1)) (hr t.1)) := by
  let Y := F ∘ periodTorusProjection L
  let D := fderiv ℝ Y
  have hpD (z v : ℂ) (hv : v ∈ L.lattice) : D (z+v) = D z := by
    have hYp : (fun w => Y (w+v)) = Y := by
      funext w
      exact congrArg F (QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using hv))
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := Y) (x := z) v
    rw [hYp] at h
    exact h.symm
  let P : C(ℂ,OrthonormalTangentPair) := ⟨fun z => spatialDifferentialFrame (hi z) (v := 1) one_ne_zero,
    spatialDifferentialFrame_continuous hD continuous_const hi (fun _ => one_ne_zero)⟩
  have hPp (z v : ℂ) (hv : v ∈ L.lattice) : P (z+v) = P z := by
    apply Subtype.ext
    change spatialGramFrame (D (z+v) 1) (D (z+v) (I*1)) = _
    rw [hpD z v hv]
    rfl
  obtain ⟨q,hq,hper⟩ := (torus_frame_global_lift_iff L P hPp).mpr (by
    intro i
    let Di : C(unitInterval,ℂ →L[ℝ] (Fin 3 → ℝ)) := ⟨fun t => D (periodBasisLine L i t),
      hD.comp ((show Continuous (periodBasisLine L i) from continuous_iff_continuousAt.mpr fun t =>
        (periodBasisLine_hasDerivAt L i t).continuousAt).comp continuous_subtype_val)⟩
    have hDi (t : unitInterval) := hi (periodBasisLine L i t)
    have hDie : Di 1 = Di 0 := by
      change D (periodBasisLine L i 1) = D (periodBasisLine L i 0)
      rw [show periodBasisLine L i 1 = periodBasisLine L i 0+L.basis i by
        simpa only [zero_add] using periodBasisLine_add_one L i 0]
      exact hpD _ _ ((periodGeneratorPeriod_val L i) ▸ (periodGeneratorPeriod L i).2)
    have hmark : SpatialFrameCurveCloses (fun t => spatialDifferentialFrame (hDi t) (L.basis.ne_zero i)) := by
      obtain ⟨g,hc,hg⟩ := hgen i
      exact ⟨g,hc,fun t => Subtype.ext (hg t)⟩
    exact regular_frame_closed_change_constant Di hDi hDie (L.basis.ne_zero i) one_ne_zero hmark)
  let V : C(unitInterval,ℂ →L[ℝ] (Fin 3 → ℝ)) := ⟨fun t => D (ξ t.1),hD.comp (hξ.continuous.comp continuous_subtype_val)⟩
  have hv (t : unitInterval) := hi (ξ t.1)
  have hξe : ξ 1 = ξ 0+ω := by simpa only [zero_add] using hp 0
  have hVe : V 1 = V 0 := by
    change D (ξ 1) = D (ξ 0)
    rw [hξe,hpD _ _ hωL]
  apply essential_frame_closed_of_fixed_direction hξ hω hp hr hinj V hv hVe
  refine ⟨⟨fun t => q (ξ t.1),q.continuous.comp (hξ.continuous.comp continuous_subtype_val)⟩,
    ?_,fun t => hq _⟩
  change q (ξ 1) = q (ξ 0)
  rw [hξe,hper _ _ hωL]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torus_ambient_lifts_along_essential_curve
