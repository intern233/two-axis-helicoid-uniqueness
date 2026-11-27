import TwoAxisHelicoid.OpenCoreSmoothTransport
import TwoAxisHelicoid.SpatialSheetInverseGerms

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff Manifold

/-- Smooth representatives of the two topological core generators lift
to genuine generating arcs in the moving period lattice. The source
marking is merely an open embedding. -/
theorem smooth_curves_of_core_homotopies {A L : PeriodPair} (C : TorusGeneratingCoreModel A)
    (j : C.carrier → PeriodTorus L) (oj : IsOpenEmbedding j)
    (c : Fin 2 → Path (j C.base) (j C.base))
    (hom : ∀ i, ((C.loop i).map oj.continuous).Homotopic (c i))
    (p : Fin 2 → ℝ → PeriodTorus L) (smooth : ∀ i, ContMDiff 𝓘(ℝ) 𝓘(ℝ,ℂ) 1 (p i))
    (same : ∀ i (t : unitInterval), p i t=c i t) (away : ∀ i t, p i t≠0) :
    ∃ D : SmoothGeneratingTorusCurves L, ∀ i t, periodTorusProjection L ((D.arc i).curve t)=p i t := by
  obtain ⟨_,_,_,gen,_⟩ := C.ambient_detection j oj
  have hgen : ∀ v : FundamentalGroup (PeriodTorus L) (j C.base), ∃ m n : ℤ,
      v=(FundamentalGroup.fromPath (.mk (c 0)))^m*(FundamentalGroup.fromPath (.mk (c 1)))^n := by
    intro v
    obtain ⟨m,n,e⟩ := gen v
    change v=(FundamentalGroup.fromPath (.mk ((C.loop 0).map oj.continuous)))^m*
      (FundamentalGroup.fromPath (.mk ((C.loop 1).map oj.continuous)))^n at e
    exact ⟨m,n,by simpa only [Path.Homotopic.Quotient.eq.mpr (hom 0),Path.Homotopic.Quotient.eq.mpr (hom 1)] using e⟩
  obtain ⟨z,hz⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) (j C.base)
  have start (i : Fin 2) : periodTorusProjection L z=p i 0 := hz.trans ((same i 0).trans (c i).source).symm
  choose arc h₀ h₁ lift proj using fun i => smooth_torus_curve_has_period_arc L (p i) (smooth i) z (start i) (fun t _ => away i t)
  have castGen {a b : PeriodTorus L} (eq : a=b) (d : Fin 2 → Path b b) (gen : ∀ v : FundamentalGroup (PeriodTorus L) b, ∃ m n : ℤ,
      v=(FundamentalGroup.fromPath (.mk (d 0)))^m*(FundamentalGroup.fromPath (.mk (d 1)))^n) :
      ∀ v : FundamentalGroup (PeriodTorus L) a, ∃ m n : ℤ, v=(FundamentalGroup.fromPath (.mk ((d 0).cast eq eq)))^m*
        (FundamentalGroup.fromPath (.mk ((d 1).cast eq eq)))^n := by subst b; exact gen
  exact ⟨⟨z,fun i => (c i).cast hz hz,arc,h₀,h₁,lift,fun i t => (proj i t).trans (same i t),castGen hz c hgen⟩,proj⟩

/-- Regularity of an actual spatial curve on an embedded normalized
surface implies regularity of its continuous punctured-torus lift. -/
theorem embedded_pitch_smooth_curve_of_position (W : PitchNormalizedBasicImmersion) (mem : W∈embeddedPitchFamily)
    (q : ℝ → PuncturedPeriodTorus (rhombicPeriodPair W.t W.ht)) (c : Continuous q)
    (sm : ContDiff ℝ 1 (fun t => W.torusPosition (q t).1)) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ,ℂ) 1 (fun t => (q t).1) := by
  intro t
  obtain ⟨G,sg,inverse⟩ := embedded_pitch_ambient_inverse_germ W mem (q t)
  have agree : (fun u => G (W.torusPosition (q u).1))=ᶠ[𝓝 t] (fun u => (q u).1) := c.continuousAt.eventually inverse
  exact (sg.comp t (contMDiffAt_iff_contDiffAt.mpr sm.contDiffAt)).congr_of_eventuallyEq agree.symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_curves_of_core_homotopies
#print axioms TwoAxisHelicoid.embedded_pitch_smooth_curve_of_position
