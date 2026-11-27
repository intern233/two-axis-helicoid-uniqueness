import TwoAxisHelicoid.RegularAnalyticSurfaceLift
import TwoAxisHelicoid.AnalyticCauchyRiemannContinuation
import TwoAxisHelicoid.TorusAntiholomorphicPuncture
import TwoAxisHelicoid.PlanePolygonPrimitive

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate

theorem period_lattice_complement_preconnected (L : PeriodPair) :
    IsPreconnected (L.lattice : Set ℂ)ᶜ := by
  have hcount : (L.lattice : Set ℂ).Countable := countable_of_Lindelof_of_discrete (X := L.lattice)
  exact (hcount.isConnected_compl_of_one_lt_rank
    (by rw [← Module.finrank_eq_rank,Complex.finrank_real_complex]; norm_num : 1 < Module.rank ℝ ℂ)).isPreconnected

/-- A continuous punctured-torus symmetry of a regular real analytic immersion
is anti-holomorphic throughout if it represents an analytic spatial symmetry
and is anti-holomorphic on one chart. -/
theorem punctured_torus_spatial_symmetry_antiholomorphic (L : PeriodPair)
    (X : PeriodTorus L → Fin 3 → ℝ) (R : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hR : ∀ p, AnalyticAt ℝ R p)
    (hY : ∀ z ∉ L.lattice, AnalyticAt ℝ (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (f : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus L)
    (hf : ∀ p : PuncturedPeriodTorus L, X (f p).1 = R (X p.1))
    {b : ℂ} (hb : b ∉ L.lattice) {G : ℂ → ℂ} (hG : AnalyticAt ℂ G (conj b))
    (hpatch : ∀ᶠ w in 𝓝 b, ∀ hw : w ∉ L.lattice,
      periodTorusProjection L (G (conj w)) = (f (puncturedPlaneProjection L ⟨w,hw⟩)).1) :
    PuncturedTorusAntiholomorphic L L f := by
  let g := compactPunctureExtension f
  obtain ⟨F,hF,_,hl⟩ := torus_continuous_map_has_lift L L g.continuous 0 0 (by
    simpa only [periodTorusProjection,QuotientAddGroup.mk_zero] using (compactPunctureExtension_at_end f).symm)
  let Y := X ∘ periodTorusProjection L
  have he (w : ℂ) (hw : w ∉ L.lattice) :
      periodTorusProjection L (F w) = (f (puncturedPlaneProjection L ⟨w,hw⟩)).1 :=
    (hl w).trans (compactPunctureExtension_apply f (puncturedPlaneProjection L ⟨w,hw⟩))
  have ha (z : ℂ) (hz : z ∉ L.lattice) : AnalyticAt ℝ F z := by
    have hn : F z ∉ L.lattice := fun h => (f (puncturedPlaneProjection L ⟨z,hz⟩)).2
      ((he z hz).symm.trans ((periodTorusProjection_eq_zero L _).mpr h))
    apply continuous_regular_surface_lift_analytic (Y := Y) (V := R ∘ Y)
      (hY _ hn).1 (hY _ hn).2 ((hR _).comp (hY _ hz).1) hF.continuousAt
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact (congrArg X (he w hw)).trans (hf (puncturedPlaneProjection L ⟨w,hw⟩))
  let K := fun z => F (conj z)
  let D := conjugatePeriodPair L
  have hb' : conj b ∉ D.lattice := by
    rw [conjugatePeriodPair_mem_iff,starRingEnd_self_apply]
    exact hb
  have hK : AnalyticOnNhd ℝ K (D.lattice : Set ℂ)ᶜ := fun z hz =>
    (ha (conj z) (fun h => hz ((conjugatePeriodPair_mem_iff L z).mpr h))).comp
      (conjCLE.toContinuousLinearMap.analyticAt z)
  have hnc : ∀ᶠ w in 𝓝 (conj b), conj w ∉ L.lattice :=
    (continuous_conj.continuousAt (x := conj b)).eventually (show ∀ᶠ y in 𝓝 (conj (conj b)), y ∉ L.lattice by
      rw [starRingEnd_self_apply]
      exact L.isClosed_lattice.isOpen_compl.mem_nhds hb)
  have hpatch' : ∀ᶠ w in 𝓝 (conj b), ∀ h : conj w ∉ L.lattice,
      periodTorusProjection L (G w) = (f (puncturedPlaneProjection L ⟨conj w,h⟩)).1 := by
    have hec : ∀ᶠ u in 𝓝 (conj (conj b)), ∀ hu : u ∉ L.lattice,
        periodTorusProjection L (G (conj u)) = (f (puncturedPlaneProjection L ⟨u,hu⟩)).1 := by
      simpa using hpatch
    simpa only [starRingEnd_self_apply] using continuous_conj.continuousAt.eventually hec
  have hm : ∀ᶠ w in 𝓝 (conj b), K w-G w ∈ L.lattice := by
    filter_upwards [hnc,hpatch'] with w hw hwp
    exact (periodTorusProjection_eq_iff L (G w) (K w)).mp ((hwp hw).trans (he (conj w) hw).symm)
  have hd := continuousAt_eventually_lattice_constant L ((hK _ hb').continuousAt.sub hG.continuousAt) hm
  have hKb : AnalyticAt ℂ K (conj b) := by
    apply (hG.add (analyticAt_const (v := K (conj b)-G (conj b)))).congr
    filter_upwards [hd] with w hw
    change K w-G w = K (conj b)-G (conj b) at hw
    change G w+(K (conj b)-G (conj b)) = K w
    linear_combination -hw
  have hall := analytic_complex_of_open_patch D.isClosed_lattice.isOpen_compl
    (period_lattice_complement_preconnected D) hK hb' hKb
  intro z hz
  have hn : conj z ∉ D.lattice := by simpa [D,conjugatePeriodPair_mem_iff] using hz
  refine ⟨K,hall _ hn,Eventually.of_forall fun w hw => ?_⟩
  simpa [K] using he w hw

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.punctured_torus_spatial_symmetry_antiholomorphic
