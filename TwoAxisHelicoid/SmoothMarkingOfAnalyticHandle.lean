import TwoAxisHelicoid.CollarFilledFiniteSmooth
import TwoAxisHelicoid.SmoothAnalyticCollarPuncture
import TwoAxisHelicoid.UnmarkedAnalyticAnnularCollar
import TwoAxisHelicoid.GenusOneFromAnnularUniformization
import TwoAxisHelicoid.MarkedPuncturedUniformization
import TwoAxisHelicoid.HolomorphicCurveRealSmooth

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology ContDiff Manifold

/-- Every Riemann surface of topological type once-punctured torus is
smoothly diffeomorphic to a punctured flat torus, including the case in
which the original complex end has finite conformal modulus. -/
theorem smooth_marking_of_analytic_handle {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀) :
    ∃ L : PeriodPair, Nonempty (Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞) := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  let _ := punctured_complex_curve_noncompact (0:PeriodTorus L₀)
  let _ : NoncompactSpace M := ⟨fun h => noncompact_univ (PuncturedPeriodTorus L₀)
    (by simpa only [image_univ,top.surjective.range_eq] using h.image top.continuous)⟩
  obtain ⟨c,r,R,hr,rr,hol,core,img,lim⟩ := unmarked_analytic_handle_round_collar top
  let s := (r+R)/2
  have rs : r<s := by dsimp [s]; linarith
  have sr : s<R := by dsimp [s]; linarith
  obtain ⟨E,d,rad,chart,src,ds,fw,bw,_,back⟩ := real_smooth_puncture_of_round_collar c hr rs sr core img lim
  obtain ⟨U,op,covers,outer⟩ := E.outer_collar_open (rad.symm ▸ sr)
  have same (x : M) (hu : x∈U) (hx : x∈E.coord.source) : E.coord x=c x := by
    have cx : c x∈d.source := ds.symm ▸ c.map_source (src ▸ hx)
    have eqn : E.coord x=d (c x) := chart ▸ rfl
    exact (back _ (outer x hu hx).le).symm.trans ((congrArg d.symm eqn).trans (d.left_inv cx))
  have man := collarFilledAtlas_isManifold E U op covers c hol src same
  have forward (x : M) (hx : x∈E.coord.source) : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ E.coord x := by
    rw [chart] at hx ⊢
    exact (contMDiffAt_iff_contDiffAt.mpr (fw _ hx.2)).comp x
      (curve_map_real_smooth_at_of_holomorphic (contMDiffAt_of_mem_maximalAtlas hol hx.1))
  have inverse (z : ℂ) (hz : z∈E.coord.target) : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ E.coord.symm z := by
    rw [chart] at hz ⊢
    exact (curve_map_real_smooth_at_of_holomorphic (contMDiffAt_symm_of_mem_maximalAtlas hol hz.2)).comp z
      (contMDiffAt_iff_contDiffAt.mpr (bw z hz.1))
  let _ := collarFilledAtlas E U op covers
  let _ : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := man
  have finite := collarFilledAtlas_real_finite_points E U op covers man forward inverse
  let marking := top.onePointCongr.trans (punctureCompactification (0:PeriodTorus L₀))
  obtain ⟨L,H,h0,hH,hi⟩ := compact_uniformization_mark_point
    (compact_torus_uniformization_from_an_annulus marking annular_riemann_surface_uniformization_proved) OnePoint.infty
  let f := markedPuncturedUniformization H h0
  have fwd : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f := by
    intro x
    rw [← contMDiffWithinAt_univ]
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U:=puncturedPeriodTorusOpen L) f univ x).mp
    exact (((holomorphic_curve_map_real_smooth hH).contMDiffAt).comp x (finite x).1).contMDiffWithinAt
  let g := fun q : PuncturedPeriodTorus L => H.symm q.1
  have hg : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ g :=
    (holomorphic_curve_map_real_smooth hi).comp (contMDiff_subtype_val (U:=puncturedPeriodTorusOpen L))
  have samePoint (q : PuncturedPeriodTorus L) : g q=(f.symm q:OnePoint M) := by
    apply H.injective
    change H (H.symm q.1)=H (f.symm q:OnePoint M)
    rw [H.apply_symm_apply,← markedPuncturedUniformization_coe H h0]
    exact congrArg Subtype.val (f.apply_symm_apply q).symm
  have bwd : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f.symm := by
    intro q
    have h := (finite (f.symm q)).2
    rw [← samePoint q] at h
    apply (h.comp q hg.contMDiffAt).congr_of_eventuallyEq
    exact Eventually.of_forall fun a => by
      change f.symm a=(g a).elim _ id
      rw [samePoint a]
      rfl
  exact ⟨L,⟨⟨f.toEquiv,fwd,bwd⟩⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_marking_of_analytic_handle

