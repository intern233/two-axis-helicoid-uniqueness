import TwoAxisHelicoid.HorizontalLineCoordinates
import TwoAxisHelicoid.TorusHorizontalSchwarzSymmetry
import TwoAxisHelicoid.HarmonicTangentLaplacian

namespace TwoAxisHelicoid
open Complex Matrix Set Filter InnerProductSpace Topology
open scoped Topology ComplexConjugate

/-- The Euclidean coordinate change which straightens a horizontal line
preserves all harmonic conformal regularity of a spatial chart. -/
theorem lineAxisCoordinates_harmonic_chart (c : ℂ) (hc : ‖c‖ = 1) (A : Fin 3 → ℝ)
    {X : ℂ → Fin 3 → ℝ} {z : ℂ} (hh : ∀ j, HarmonicAt (fun w => X w j) z)
    (hcon : ConformalCoordinateDerivatives X z) (hi : Function.Injective (fderiv ℝ X z)) :
    let Y := lineAxisCoordinates c hc A ∘ X
    (∀ j, HarmonicAt (fun w => Y w j) z) ∧ ConformalCoordinateDerivatives Y z ∧
      Function.Injective (fderiv ℝ Y z) := by
  let R := verticalRotation (conj c)
  let Y := lineAxisCoordinates c hc A ∘ X
  have hx : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hh j)
  have hhv : HarmonicAt X z := by
    refine ⟨hx.contDiffAt,?_⟩
    have he : ∀ᶠ w in 𝓝 z, ∀ j, HarmonicAt (fun y => X y j) w := by
      rw [eventually_all]
      exact fun j => (isOpen_setOfPred_harmonicAt (f := fun y => X y j)).mem_nhds (hh j)
    exact he.mono fun w hw => harmonic_coordinate_laplacian_zero hw
  have hsub := hhv.sub (harmonicAt_const A)
  have hY : HarmonicAt Y z := hsub.comp_CLM R
  have hd : HasFDerivAt Y (R.comp (fderiv ℝ X z)) z :=
    R.hasFDerivAt.comp z (hx.differentiableAt.hasFDerivAt.sub_const A)
  have hR : Function.Injective R := (unitVerticalRotation (conj c) (by simpa)).injective
  refine ⟨fun j => hY.comp_CLM (ContinuousLinearMap.proj j),?_,?_⟩
  · apply (conformalCoordinateDerivatives_iff_dot hd.differentiableAt).mpr
    obtain ⟨hm,ho⟩ := (conformalCoordinateDerivatives_iff_dot hx.differentiableAt).mp hcon
    rw [hd.fderiv]
    simpa only [ContinuousLinearMap.comp_apply,R,verticalRotation_preserves_dot (c := conj c) (by simpa)] using And.intro hm ho
  · rw [hd.fderiv]
    exact hR.comp hi

/-- Schwarz reflection for a horizontal straight line at an arbitrary position
and angle on the embedded torus, expressed in the original spatial frame. -/
theorem embedded_torus_reflects_horizontal_line (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (c : ℂ) (hc : ‖c‖ = 1) (A : Fin 3 → ℝ)
    (hline : ∀ s : ℝ, A+s • ![c.re,c.im,0] ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z)) :
    MapsTo (horizontalLineHalfTurn A ![c.re,c.im,0])
      (range (fun q : PuncturedPeriodTorus L => X q.1)) (range (fun q : PuncturedPeriodTorus L => X q.1)) := by
  let R := lineAxisCoordinates c hc A
  have hs (s : ℝ) : (![s,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => R (X q.1)) := by
    obtain ⟨q,hq⟩ := hline s
    exact ⟨q,(congrArg R hq).trans (lineAxisCoordinates_line c hc A s)⟩
  obtain ⟨f,_,hf⟩ := closed_embedded_torus_horizontal_schwarz L (R ∘ X) (R.isClosedEmbedding.comp hX) hs
    (fun z hz => lineAxisCoordinates_harmonic_chart c hc A (hhi z hz).1 (hhi z hz).2.1 (hhi z hz).2.2)
  rintro _ ⟨q,rfl⟩
  exact ⟨f q,R.injective ((hf q).trans (lineAxisCoordinates_half_turn c hc A (X q.1)).symm)⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.embedded_torus_reflects_horizontal_line
