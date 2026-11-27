import TwoAxisHelicoid.EmbeddedStraightAxisReflection
import TwoAxisHelicoid.ActualTorusManifoldDifferential
import TwoAxisHelicoid.PuncturedLatticePlane

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ComplexConjugate

/-- On a neighborhood of the actual punctured chart center the coordinate
projection is precisely the lattice quotient. -/
theorem punctured_chart_projects (L : PeriodPair) (q : PuncturedPeriodTorus L) :
    ∀ᶠ w in 𝓝 (chartAt ℂ q q), ((chartAt ℂ q).symm w).1 = periodTorusProjection L w := by
  have hcharts := TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
    (H := ℂ) (puncturedPeriodTorusOpen L) (x := q)
  filter_upwards [hcharts] with w hw
  change (chartAt ℂ q.1).symm w = ((chartAt ℂ q).symm w).1 at hw
  rw [← hw,periodTorus_chart_symm_eq_projection]

theorem ConformalCoordinateDerivatives.congr {Y Z : ℂ → Fin 3 → ℝ} {z : ℂ}
    (h : ConformalCoordinateDerivatives Y z) (he : Y =ᶠ[𝓝 z] Z) : ConformalCoordinateDerivatives Z z := by
  have hf (j : Fin 3) : fderiv ℝ (fun w => Y w j) z = fderiv ℝ (fun w => Z w j) z :=
    (show (fun w => Y w j) =ᶠ[𝓝 z] (fun w => Z w j) from he.mono (fun w hw => congrFun hw j)).fderiv_eq
  simpa only [ConformalCoordinateDerivatives,← hf] using h

theorem punctured_chart_image_local_equation (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (hY : ∀ z ∉ L.lattice, AnalyticAt ℝ (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z)) :
    ∀ p ∈ range (fun q : PuncturedPeriodTorus L => X q.1),
      ∃ G : (Fin 3 → ℝ) → Fin 3 → ℝ, AnalyticAt ℝ G p ∧
        ∀ᶠ v in 𝓝 p, v ∈ range (fun q : PuncturedPeriodTorus L => X q.1) ↔ G v = 0 := by
  rintro _ ⟨q,rfl⟩
  let e := chartAt ℂ q
  have hloc : (fun w => X (periodTorusProjection L w)) =ᶠ[𝓝 (e q)] (fun w => X (e.symm w).1) :=
    (punctured_chart_projects L q).mono fun _ h => congrArg X h.symm
  obtain ⟨ha,hi⟩ := hY (e q) (puncturedPeriodTorus_chart_not_lattice L q)
  exact embedded_analytic_surface_local_equation hX e (mem_chart_source ℂ q) (ha.congr hloc)
    (hloc.fderiv_eq (𝕜 := ℝ) ▸ hi)

/-- An embedded harmonic conformal parametrization that contains the axis
induces an actual antiholomorphic germ in quotient coordinates. -/
theorem punctured_chart_horizontal_reflection_germ (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (haxis : ∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z)) :
    ∃ b ∉ L.lattice, ∃ G : ℂ → ℂ, AnalyticAt ℂ G (conj b) ∧ G (conj b) = b ∧
      ∀ᶠ w in 𝓝 b, G (conj w) ∉ L.lattice ∧
        X (periodTorusProjection L (G (conj w))) = halfTurnX (X (periodTorusProjection L w)) := by
  obtain ⟨q,hq⟩ := haxis 0
  change X q.1 = ![0,0,0] at hq
  have hq0 : X q.1 = 0 := hq.trans (by ext j; fin_cases j <;> rfl)
  let e := chartAt ℂ q
  let b := e q
  let Y := X ∘ periodTorusProjection L
  let Z := fun w => X (e.symm w).1
  have hb : b ∉ L.lattice := puncturedPeriodTorus_chart_not_lattice L q
  have he : Y =ᶠ[𝓝 b] Z := (punctured_chart_projects L q).mono fun _ h => congrArg X h.symm
  have ha : AnalyticAt ℝ Y b := analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt ((hhi b hb).1 j))
  have hlocal : ∀ᶠ w in 𝓝 b, (∀ j, HarmonicAt (fun v => Z v j) w) ∧
      ConformalCoordinateDerivatives Z w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hb,he.eventually_nhds] with w hw hwe
    exact ⟨fun j => (harmonicAt_congr_nhds (hwe.mono fun v hv => congrFun hv j)).mp ((hhi w hw).1 j),
      (hhi w hw).2.1.congr hwe⟩
  obtain ⟨G,hG,hGb,hGr⟩ := embedded_axis_local_reflection hX e (mem_chart_source ℂ q) hq0 haxis
    (ha.congr he) (he.fderiv_eq (𝕜 := ℝ) ▸ (hhi b hb).2.2) hlocal
  refine ⟨b,hb,G,hG,hGb,?_⟩
  have ht : Tendsto (fun w => G (conj w)) (𝓝 b) (𝓝 b) := by
    have htc : Tendsto (fun w => G (conj w)) (𝓝 b) (𝓝 (G (conj b))) := hG.continuousAt.tendsto.comp continuous_conj.continuousAt
    simpa only [show G (conj b) = b from hGb] using htc
  filter_upwards [hGr,he,ht.eventually he,ht.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds hb)] with w hw h1 h2 hw'
  exact ⟨hw',h2.trans (hw.2.trans (congrArg halfTurnX h1.symm))⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.punctured_chart_horizontal_reflection_germ
