import TwoAxisHelicoid.EmbeddedTorusChartReflection
import TwoAxisHelicoid.TorusSpatialSymmetryContinuation
import TwoAxisHelicoid.PuncturedAxesNormalization

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ComplexConjugate

theorem halfTurnX_analyticAt (v : Fin 3 → ℝ) : AnalyticAt ℝ halfTurnX v := by
  apply analyticAt_pi_iff.mpr
  intro j
  fin_cases j
  · exact (ContinuousLinearMap.proj 0 : (Fin 3 → ℝ) →L[ℝ] ℝ).analyticAt _
  · exact (ContinuousLinearMap.proj 1 : (Fin 3 → ℝ) →L[ℝ] ℝ).analyticAt _ |>.neg
  · exact (ContinuousLinearMap.proj 2 : (Fin 3 → ℝ) →L[ℝ] ℝ).analyticAt _ |>.neg

/-- The whole spatial Schwarz reflection and its domain anti-holomorphicity
follow from an embedded harmonic conformal immersion containing the line. -/
theorem closed_embedded_torus_horizontal_schwarz (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (haxis : ∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z)) :
    ∃ (f : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus L),
      PuncturedTorusAntiholomorphic L L f ∧ ∀ q, X (f q).1 = halfTurnX (X q.1) := by
  let Y := X ∘ periodTorusProjection L
  let Z := fun q : PuncturedPeriodTorus L => X q.1
  have hY (z : ℂ) (hz : z ∉ L.lattice) : AnalyticAt ℝ Y z ∧ Function.Injective (fderiv ℝ Y z) :=
    ⟨analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((hhi z hz).1 j)),(hhi z hz).2.2⟩
  obtain ⟨b,hb,G,hG,_,hpatch⟩ := punctured_chart_horizontal_reflection_germ L X hX.isEmbedding haxis hhi
  have himage : MapsTo (halfTurnX ∘ Y) (L.lattice : Set ℂ)ᶜ (range Z) := by
    apply analytic_image_continues_in_closed_hypersurface L.isClosed_lattice.isOpen_compl
      (period_lattice_complement_preconnected L) (fun w hw => (halfTurnX_analyticAt _).comp (hY w hw).1)
      hX.isClosed_range (punctured_chart_image_local_equation L X hX.isEmbedding hY) hb
    filter_upwards [hpatch] with w hw
    exact ⟨puncturedPlaneProjection L ⟨G (conj w),hw.1⟩,hw.2⟩
  have hspatial (q : PuncturedPeriodTorus L) : halfTurnX (Z q) ∈ range Z := by
    obtain ⟨w,rfl⟩ := puncturedPlaneProjection_surjective L q
    exact himage w.property
  let f := embeddedRangeInvolution hX.isEmbedding halfTurnX halfTurnX_continuous halfTurnX_involutive hspatial
  have he (q : PuncturedPeriodTorus L) : Z (f q) = halfTurnX (Z q) :=
    embeddedRangeInvolution_eq hX.isEmbedding halfTurnX halfTurnX_continuous halfTurnX_involutive hspatial q
  refine ⟨f,?_,he⟩
  apply punctured_torus_spatial_symmetry_antiholomorphic L X halfTurnX halfTurnX_analyticAt hY f he hb hG
  filter_upwards [hpatch] with w hw hn
  let q := puncturedPlaneProjection L ⟨w,hn⟩
  let r := puncturedPlaneProjection L ⟨G (conj w),hw.1⟩
  have hh : Z r = Z (f q) := hw.2.trans (he q).symm
  exact congrArg Subtype.val (hX.injective hh)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.closed_embedded_torus_horizontal_schwarz
