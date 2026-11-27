import TwoAxisHelicoid.TorusHorizontalSchwarzSymmetry

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ComplexConjugate

/-- Interchange the horizontal and vertical coordinate axes. -/
noncomputable def schwarzSwapXZ : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ) :=
  (show (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) from
    { toFun := fun v => ![v 2,v 1,v 0]
      invFun := fun v => ![v 2,v 1,v 0]
      left_inv := fun v => by ext j; fin_cases j <;> rfl
      right_inv := fun v => by ext j; fin_cases j <;> rfl
      map_add' := fun v w => by ext j; fin_cases j <;> rfl
      map_smul' := fun r v => by ext j; fin_cases j <;> rfl }).toContinuousLinearEquiv

theorem conformalCoordinateDerivatives_swapXZ {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ConformalCoordinateDerivatives X z) :
    ConformalCoordinateDerivatives (schwarzSwapXZ ∘ X) z := by
  rcases hX with ⟨hr,hi⟩
  unfold ConformalCoordinateDerivatives
  simp only [Fin.sum_univ_succ] at hr hi ⊢
  constructor
  · convert hr using 1 <;> dsimp [schwarzSwapXZ] <;> ring
  · convert hi using 1
    dsimp [schwarzSwapXZ]
    ring

theorem closed_embedded_torus_vertical_schwarz (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (haxis : ∀ s : ℝ, (![0,0,s] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z)) :
    ∃ (f : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus L),
      PuncturedTorusAntiholomorphic L L f ∧ ∀ q, X (f q).1 = halfTurnZ (X q.1) := by
  let Z := schwarzSwapXZ ∘ X
  let Y := X ∘ periodTorusProjection L
  have hZ : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => Z q.1) :=
    schwarzSwapXZ.toHomeomorph.isClosedEmbedding.comp hX
  have hline (s : ℝ) : (![s,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => Z q.1) := by
    obtain ⟨q,hq⟩ := haxis s
    exact ⟨q,congrArg schwarzSwapXZ hq⟩
  have hdata (z : ℂ) (hz : z ∉ L.lattice) :
      (∀ j, HarmonicAt (fun w => Z (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (Z ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (Z ∘ periodTorusProjection L) z) := by
    obtain ⟨hh,hc,hi⟩ := hhi z hz
    have ha : AnalyticAt ℝ Y z := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (hh j))
    refine ⟨?_,conformalCoordinateDerivatives_swapXZ hc,?_⟩
    · intro j
      fin_cases j
      · exact hh 2
      · exact hh 1
      · exact hh 0
    · have hd := schwarzSwapXZ.toContinuousLinearMap.hasFDerivAt.comp z ha.differentiableAt.hasFDerivAt
      change Function.Injective (fderiv ℝ (schwarzSwapXZ.toContinuousLinearMap ∘ Y) z)
      rw [hd.fderiv]
      exact schwarzSwapXZ.injective.comp hi
  obtain ⟨f,hf,he⟩ := closed_embedded_torus_horizontal_schwarz L Z hZ hline hdata
  refine ⟨f,hf,fun q => ?_⟩
  apply schwarzSwapXZ.injective
  calc
    schwarzSwapXZ (X (f q).1) = halfTurnX (schwarzSwapXZ (X q.1)) := he q
    _ = schwarzSwapXZ (halfTurnZ (X q.1)) := by ext j; fin_cases j <;> rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.closed_embedded_torus_vertical_schwarz
