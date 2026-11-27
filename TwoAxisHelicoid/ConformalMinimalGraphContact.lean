import TwoAxisHelicoid.ConformalGraphDifference
import TwoAxisHelicoid.OrderedDriftContact

namespace TwoAxisHelicoid
open Complex Filter Set Topology Matrix InnerProductSpace Laplacian
open scoped Topology ContDiff

private theorem graphDifferenceDrift_continuousAt {T : Type*} [TopologicalSpace T] {t : T}
    {A B : T → Fin 3 → ℝ} {G : T → ℂ →L[ℝ] ℝ} {D : T → ℂ →L[ℝ] ℂ →L[ℝ] ℝ}
    (a : ContinuousAt A t) (b : ContinuousAt B t) (g : ContinuousAt G t) (d : ContinuousAt D t) :
    ContinuousAt (fun w => graphDifferenceDrift (A w) (B w) (G w) (D w)) t := by
  have aa (j : Fin 3) : ContinuousAt (fun w => A w j) t := (continuous_apply j).continuousAt.comp a
  have bb (j : Fin 3) : ContinuousAt (fun w => B w j) t := (continuous_apply j).continuousAt.comp b
  have gg (v : ℂ) : ContinuousAt (fun w => G w v) t :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.continuousAt.comp g
  have dd (v u : ℂ) : ContinuousAt (fun w => D w v u) t :=
    (ContinuousLinearMap.apply ℝ ℝ u).continuous.continuousAt.comp
      ((ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] ℝ) v).continuous.continuousAt.comp d)
  simp only [graphDifferenceDrift,horizontalMinor]
  fun_prop

/-- In the immersion's conformal parameter, the difference from an
analytic minimal graph solves a linear drift equation with continuous
coefficients near every regular point. -/
theorem harmonic_immersion_graph_difference_local_drift {X : ℂ → Fin 3 → ℝ} {g : ℂ → ℝ} {z : ℂ}
    (hX : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun v => X v j) w) ∧ ConformalCoordinateDerivatives X w)
    (hi : Function.Injective (fderiv ℝ X z)) (hg : AnalyticAt ℝ g (spatialGraphProjection 0 1 (X z)))
    (hm : ∀ᶠ w in 𝓝 (spatialGraphProjection 0 1 (X z)), cartesianMinimalGraphOperator g w=0)
    : ∃ A B : ℂ → ℝ, ContinuousAt A z ∧ ContinuousAt B z ∧
      ∀ᶠ w in 𝓝 z, (Δ (immersionGraphDifference X g)) w =
        A w*planePartial 1 (immersionGraphDifference X g) w+B w*planePartial I (immersionGraphDifference X g) w := by
  let U := spatialGraphProjection 0 1 ∘ X
  let A := planePartial 1 X
  let B := planePartial I X
  let l := fun w => A w ⬝ᵥ A w
  let W := fun w => graphDifferenceDrift (A w) (B w) (fderiv ℝ g (U w)) (fderiv ℝ (fderiv ℝ g) (U w))
  let dx := fun w => (W w).1/l w
  let dy := fun w => (W w).2/l w
  have p := hX.self_of_nhds
  have ax : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (p.1 j))
  have au : AnalyticAt ℝ U z := ((spatialGraphProjection 0 1).analyticAt _).comp ax
  have aa : AnalyticAt ℝ A z := planePartial_analyticAt ax 1
  have ba : AnalyticAt ℝ B z := planePartial_analyticAt ax I
  have la : AnalyticAt ℝ l z := (spatialDotBilinear.analyticAt_bilinear (A z,A z)).comp₂ aa aa
  have pos : 0 < l z := (harmonicChartNormal_data ax p.2 hi).2.1
  have cw : ContinuousAt W z := graphDifferenceDrift_continuousAt aa.continuousAt ba.continuousAt
    (hg.fderiv.continuousAt.comp (f := U) au.continuousAt) (hg.fderiv.fderiv.continuousAt.comp (f := U) au.continuousAt)
  have cd : ContinuousAt dx z := (continuous_fst.continuousAt.comp cw).div la.continuousAt pos.ne'
  have ce : ContinuousAt dy z := (continuous_snd.continuousAt.comp cw).div la.continuousAt pos.ne'
  let f := immersionGraphDifference X g
  have eq : ∀ᶠ w in 𝓝 z, (Δ f) w = dx w*planePartial 1 f w+dy w*planePartial I f w := by
    filter_upwards [hX,au.continuousAt hg.eventually_analyticAt,au.continuousAt hm,la.continuousAt.eventually_ne pos.ne'] with w hw ag op nz
    have ident := harmonic_graph_difference_equation hw.1 hw.2 ag
    change l w*(Δ f) w = (W w).1*planePartial 1 f w+(W w).2*planePartial I f w-
      (horizontalMinor (A w) (B w))^2*cartesianMinimalGraphOperator g (U w) at ident
    rw [op,mul_zero,sub_zero] at ident
    dsimp only [dx,dy]
    field_simp [nz]
    linear_combination ident
  exact ⟨dx,dy,cd,ce,eq⟩

/-- An actual regular harmonic conformal immersion touching one side
of a minimal Cartesian graph coincides with it in a neighborhood. The
maximum principle is applied in the given conformal coordinates. -/
theorem harmonic_immersion_one_sided_minimal_graph {X : ℂ → Fin 3 → ℝ} {g : ℂ → ℝ} {z : ℂ}
    (hX : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun v => X v j) w) ∧ ConformalCoordinateDerivatives X w)
    (hi : Function.Injective (fderiv ℝ X z)) (hg : AnalyticAt ℝ g (spatialGraphProjection 0 1 (X z)))
    (hm : ∀ᶠ w in 𝓝 (spatialGraphProjection 0 1 (X z)), cartesianMinimalGraphOperator g w=0)
    (touch : immersionGraphDifference X g z=0)
    (side : (∀ᶠ w in 𝓝 z, 0 ≤ immersionGraphDifference X g w) ∨
      (∀ᶠ w in 𝓝 z, immersionGraphDifference X g w ≤ 0)) :
    ∀ᶠ w in 𝓝 z, X w 2 = g (spatialGraphProjection 0 1 (X w)) := by
  have ax : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hX.self_of_nhds.1 j)
  obtain ⟨A,B,ca,cb,eq⟩ := harmonic_immersion_graph_difference_local_drift hX hi hg hm
  exact (planar_drift_one_sided_contact (immersionGraphDifference_analytic ax hg) ca cb touch side eq).mono
    fun _ h => sub_eq_zero.mp h

/-- The Cartesian height graph of a harmonic conformal chart solves the
minimal graph equation wherever its projected minor is nonsingular. -/
theorem harmonic_immersion_graph_operator_zero {X : ℂ → Fin 3 → ℝ} {g : ℂ → ℝ} {z : ℂ}
    (hh : ∀ j, HarmonicAt (fun v => X v j) z) (hc : ConformalCoordinateDerivatives X z)
    (hg : AnalyticAt ℝ g (spatialGraphProjection 0 1 (X z)))
    (hj : horizontalMinor (planePartial 1 X z) (planePartial I X z) ≠ 0)
    (onGraph : ∀ᶠ w in 𝓝 z, X w 2=g (spatialGraphProjection 0 1 (X w))) :
    cartesianMinimalGraphOperator g (spatialGraphProjection 0 1 (X z))=0 := by
  let f := immersionGraphDifference X g
  have zero : f =ᶠ[𝓝 z] (0:ℂ → ℝ) := onGraph.mono (fun _ h => sub_eq_zero.mpr h)
  have lap : (Δ f) z=0 := by
    have eq := (laplacian_congr_nhds zero).self_of_nhds
    change (Δ f) z=(Δ (fun _ : ℂ => (0:ℝ))) z at eq
    simpa only [laplacian_const,Pi.zero_apply] using eq
  have grad (v : ℂ) : planePartial v f z=0 := by
    have e := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (zero.fderiv_eq (𝕜 := ℝ))
    simpa [planePartial] using e
  have h := harmonic_graph_difference_equation hh hc hg
  dsimp only at h
  change _*(Δ f) z = _*planePartial 1 f z+_*planePartial I f z-_ at h
  rw [lap,grad 1,grad I,mul_zero,mul_zero,mul_zero,add_zero,zero_sub] at h
  exact (mul_eq_zero.mp (neg_eq_zero.mp h.symm)).resolve_left (pow_ne_zero 2 hj)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_immersion_graph_difference_local_drift
#print axioms TwoAxisHelicoid.harmonic_immersion_one_sided_minimal_graph
#print axioms TwoAxisHelicoid.harmonic_immersion_graph_operator_zero
