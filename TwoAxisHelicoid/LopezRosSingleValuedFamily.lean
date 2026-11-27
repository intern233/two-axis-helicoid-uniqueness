import TwoAxisHelicoid.LopezRosVerticalFluxPrimitives

namespace TwoAxisHelicoid
open Complex Set Filter InnerProductSpace
open scoped Topology

/-- Global holomorphic combinations of the horizontal coordinates under
the vertical flux hypothesis. Their real parts are normalized to the
given spatial coordinates themselves, including both integration constants. -/
theorem vertical_flux_normalized_horizontal_primitives (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    (hflux : ¬ HasIntrinsicNonverticalFlux L X) :
    ∃ F : Fin 2 → ℂ → ℂ, (∀ j z ω, ω ∈ L.lattice → F j (z+ω) = F j z) ∧
      ∀ j z, z ∉ L.lattice → HasDerivAt (F j) (torusImmersionForms L X z j.castSucc) z ∧
        (F j z).re = torusFilledPosition L X (periodTorusProjection L z) j.castSucc := by
  obtain ⟨G,hp,hG⟩ := vertical_flux_horizontal_primitives L X hX hflux
  obtain ⟨_,_,hD⟩ := torusImmersionForms_regular L X (fun z hz => (hX z hz).1) (fun z hz => (hX z hz).2)
  have hc (j : Fin 2) : ∃ c : ℝ, ∀ z ∉ L.lattice,
      torusFilledPosition L X (periodTorusProjection L z) j.castSucc = (G j z).re+c := by
    let P := fun w => torusFilledPosition L X (periodTorusProjection L w) j.castSucc
    have dP (z : ℂ) (hz : z ∉ L.lattice) :
        HasFDerivAt P (realCoefficientDerivative (torusImmersionForms L X z j.castSucc)) z :=
      (ContinuousLinearMap.proj j.castSucc : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hD z hz)
    have dG (z : ℂ) (hz : z ∉ L.lattice) :
        HasFDerivAt (fun w => (G j w).re) (realCoefficientDerivative (torusImmersionForms L X z j.castSucc)) z :=
      reCLM.hasFDerivAt.comp z ((hG j z hz).hasFDerivAt.restrictScalars ℝ)
    exact L.isClosed_lattice.isOpen_compl.exists_eq_add_of_fderiv_eq
      (marked_torus_lattice_complement_connected L).isPreconnected
      (fun z hz => (dP z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (dG z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (dP z hz).fderiv.trans (dG z hz).fderiv.symm)
  choose c he using hc
  refine ⟨fun j z => G j z+(c j:ℂ),fun j z ω hω => congrArg (·+(c j:ℂ)) (hp j z ω hω),?_⟩
  intro j z hz
  refine ⟨(hG j z hz).add_const _,?_⟩
  change (G j z+(c j:ℂ)).re = _
  rw [Complex.add_re,ofReal_re,he j z hz]

/-- All nonzero complex Gauss multipliers give single-valued coordinate
maps under everywhere vertical flux. The family equals the original map
at multiplier one and has exactly the indicated horizontal Weierstrass
forms, also at vertical normals. -/
theorem vertical_flux_lopez_ros_single_valued_family (L : PeriodPair) (X : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (hX : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L X w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L X) z)
    (hflux : ¬ HasIntrinsicNonverticalFlux L X) :
    ∃ Y : ℂ → PuncturedPeriodTorus L → Fin 3 → ℝ, Y 1 = X ∧
      (∀ k q, Y k q 2 = X q 2) ∧ ∀ (k : ℂ) (j : Fin 2) (z : ℂ), z ∉ L.lattice →
        HasFDerivAt (fun w => puncturedTorusPullback L (Y k) w j.castSucc)
          (realCoefficientDerivative (lopezRosHorizontal k (torusImmersionForms L X z 0) (torusImmersionForms L X z 1) j)) z ∧
          HarmonicAt (fun w => puncturedTorusPullback L (Y k) w j.castSucc) z := by
  obtain ⟨F,hp,hF⟩ := vertical_flux_normalized_horizontal_primitives L X hX hflux
  let f (j : Fin 2) (q : PuncturedPeriodTorus L) := periodTorusLift L (F j) (hp j) q.1
  let Y (k : ℂ) (q : PuncturedPeriodTorus L) : Fin 3 → ℝ :=
    ![(lopezRosHorizontal k (f 0 q) (f 1 q) 0).re,(lopezRosHorizontal k (f 0 q) (f 1 q) 1).re,X q 2]
  have hr (j : Fin 2) (q : PuncturedPeriodTorus L) : (f j q).re = X q j.castSucc := by
    obtain ⟨z,rfl⟩ := puncturedPlaneProjection_surjective L q
    exact ((hF j z z.2).2).trans (congrFun (torusFilledPosition_eq L X (puncturedPlaneProjection L z)) j.castSucc)
  refine ⟨Y,?_,fun _ _ => rfl,?_⟩
  · funext q j
    fin_cases j
    · simpa [Y,lopezRosHorizontal,lopezRosAverage,lopezRosSkew] using! hr 0 q
    · simpa [Y,lopezRosHorizontal,lopezRosAverage,lopezRosSkew] using! hr 1 q
    · rfl
  · intro k j z hz
    let G := fun w => lopezRosHorizontal k (F 0 w) (F 1 w) j
    let d := lopezRosHorizontal k (torusImmersionForms L X z 0) (torusImmersionForms L X z 1) j
    have hd : HasDerivAt G d z := by
      fin_cases j
      · exact (((hF 0 z hz).1.const_mul _).add ((hF 1 z hz).1.const_mul _))
      · exact (((hF 1 z hz).1.const_mul _).sub ((hF 0 z hz).1.const_mul _))
    have he : (fun w => puncturedTorusPullback L (Y k) w j.castSucc) =ᶠ[𝓝 z] (fun w => (G w).re) := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      change w ∉ L.lattice at hw
      fin_cases j <;> simp [puncturedTorusPullback,hw,Y,f,G,puncturedPlaneProjection]
    have hA (i : Fin 2) : AnalyticAt ℂ (F i) z :=
      DifferentiableOn.analyticAt (fun w hw => (hF i w hw).1.differentiableAt.differentiableWithinAt)
        (L.isClosed_lattice.isOpen_compl.mem_nhds hz)
    have hG : AnalyticAt ℂ G z := by
      fin_cases j
      · exact (analyticAt_const.mul (hA 0)).add (analyticAt_const.mul (hA 1))
      · exact (analyticAt_const.mul (hA 1)).sub (analyticAt_const.mul (hA 0))
    exact ⟨(reCLM.hasFDerivAt.comp z (hd.hasFDerivAt.restrictScalars ℝ)).congr_of_eventuallyEq he,
      (harmonicAt_congr_nhds he).mpr (hG.harmonicAt.comp_CLM reCLM)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.vertical_flux_lopez_ros_single_valued_family
