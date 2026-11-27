import TwoAxisHelicoid.ConformalSurfaceLiftOrientation
import TwoAxisHelicoid.PuncturedTorusAutomorphisms
import TwoAxisHelicoid.TorusSpatialSymmetryContinuation

namespace TwoAxisHelicoid
open Complex Set Filter Matrix Topology
open scoped Topology

/-- The square of any ambient similarity inducing a homeomorphism of a
regular conformal punctured torus acts holomorphically. Orientation of the
ambient or surface action need not be supplied. -/
theorem spatial_similarity_torus_square_holomorphic (L : PeriodPair)
    (X : PeriodTorus L → Fin 3 → ℝ)
    (hY : ∀ z ∉ L.lattice, AnalyticAt ℝ (X ∘ periodTorusProjection L) z ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (R : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (hR : ∀ v, AnalyticAt ℝ R v)
    {P : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)} (hd : ∀ v, HasFDerivAt R P v)
    {k : ℝ} (hk : 0 < k) (hmetric : ∀ u v, P u ⬝ᵥ P v = k*(u ⬝ᵥ v))
    (f : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus L)
    (hf : ∀ p : PuncturedPeriodTorus L, X (f p).1 = R (X p.1)) :
    PuncturedTorusHolomorphic L L (f.trans f) := by
  let g := compactPunctureExtension f
  obtain ⟨F,hF,_,hl⟩ := torus_continuous_map_has_lift L L g.continuous 0 0 (by
    simpa only [periodTorusProjection,QuotientAddGroup.mk_zero] using (compactPunctureExtension_at_end f).symm)
  let Y := X ∘ periodTorusProjection L
  let U := (L.lattice : Set ℂ)ᶜ
  have he (z : ℂ) (hz : z ∈ U) : periodTorusProjection L (F z) = (f (puncturedPlaneProjection L ⟨z,hz⟩)).1 :=
    (hl z).trans (compactPunctureExtension_apply f (puncturedPlaneProjection L ⟨z,hz⟩))
  have hmap : MapsTo F U U := fun z hz h => (f (puncturedPlaneProjection L ⟨z,hz⟩)).2
    ((he z hz).symm.trans ((periodTorusProjection_eq_zero L _).mpr h))
  have heq (z : ℂ) (hz : z ∈ U) : Y ∘ F =ᶠ[𝓝 z] R ∘ Y := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact (congrArg X (he w hw)).trans (hf (puncturedPlaneProjection L ⟨w,hw⟩))
  have ha : AnalyticOnNhd ℝ F U := fun z hz =>
    continuous_regular_surface_lift_analytic (Y := Y) (V := R ∘ Y)
      (hY _ (hmap hz)).1 (hY _ (hmap hz)).2.2 ((hR _).comp (hY _ hz).1) hF.continuousAt (heq _ hz)
  have H := conformal_plane_square_holomorphic L.isClosed_lattice.isOpen_compl
    (period_lattice_complement_preconnected L) ha hmap (fun z hz =>
      lifted_similarity_plane_columns (hY _ hz).1.differentiableAt (hY _ (hmap hz)).1.differentiableAt
        (hY _ hz).2.1 (hY _ (hmap hz)).2.1 (hY _ hz).2.2 (hY _ (hmap hz)).2.2
        (ha _ hz).differentiableAt (hd _) hk hmetric (heq _ hz))
  intro z hz
  refine ⟨F ∘ F,H z hz,Eventually.of_forall fun w hw => ?_⟩
  have hh : puncturedPlaneProjection L ⟨F w,hmap hw⟩ = f (puncturedPlaneProjection L ⟨w,hw⟩) := Subtype.ext (he w hw)
  exact (he (F w) (hmap hw)).trans (congrArg (fun q : PuncturedPeriodTorus L => (f q).1) hh)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.spatial_similarity_torus_square_holomorphic
