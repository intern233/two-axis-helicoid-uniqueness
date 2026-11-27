import TwoAxisHelicoid.SmoothTorusCurveLift
import TwoAxisHelicoid.DisjointTorusCoreObstruction
import TwoAxisHelicoid.SmoothGeneratingCoreTransfer
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology Manifold ContDiff

noncomputable def markedTorusBasisTrajectory (A : PeriodPair) (i : Fin 2) : ℝ → PeriodTorus A :=
  periodTorusProjection A ∘ periodBasisLine A i

theorem markedTorusBasisTrajectory_smooth (A : PeriodPair) (i : Fin 2) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ,ℂ) 1 (markedTorusBasisTrajectory A i) := by
  have hp : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) 1 (periodTorusProjection A) := by
    intro z
    obtain ⟨e,hz,he⟩ := periodTorusProjection_isLocalHomeomorph A z
    have ha : e.symm ∈ atlas ℂ (PeriodTorus A) := he.symm
    rw [he]
    exact contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,ℂ)) (n := 1) (IsManifold.subset_maximalAtlas ha) hz
  apply hp.comp
  apply ContDiff.contMDiff
  unfold periodBasisLine
  fun_prop

theorem TorusGeneratingCoreModel.trajectory_mem {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    (i : Fin 2) (s : ℝ) : markedTorusBasisTrajectory A i s ∈ C.carrier := by
  let u : unitInterval := ⟨Int.fract s,Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
  have h := (periodBasisLine_periodic_projection A i).sub_zsmul_eq (x := s) ⌊s⌋
  have he : markedTorusBasisTrajectory A i (u:ℝ) = markedTorusBasisTrajectory A i s := by
    simpa only [u,Int.fract,zsmul_eq_mul,mul_one] using! congrArg Subtype.val h
  have hp : (C.loop i u).1 = markedTorusBasisTrajectory A i u := C.projects i u
  rw [← he,← hp]
  exact (C.loop i u).2

/-- A genuine smooth graph patch on the marked approximating torus. The
map may be defined arbitrarily outside the open source core. -/
structure SmoothOpenTorusCoreMap {A : PeriodPair} (C : TorusGeneratingCoreModel A) (L : PeriodPair) where
  map : PeriodTorus A → PeriodTorus L
  embedding : IsOpenEmbedding (fun q : C.carrier => map q.1)
  smooth : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) 1 map C.carrier
  avoids : ∀ q ∈ C.carrier, map q ≠ 0

noncomputable def SmoothOpenTorusCoreMap.trajectory {A L : PeriodPair} {C : TorusGeneratingCoreModel A}
    (F : SmoothOpenTorusCoreMap C L) (i : Fin 2) := F.map ∘ markedTorusBasisTrajectory A i

private theorem torus_generators_cast {L : PeriodPair} {p q : PeriodTorus L} (h : p = q)
    (γ : Fin 2 → Path q q) (hg : ∀ v : FundamentalGroup (PeriodTorus L) q, ∃ m n : ℤ,
      v = (FundamentalGroup.fromPath (.mk (γ 0)))^m*(FundamentalGroup.fromPath (.mk (γ 1)))^n) :
    ∀ v : FundamentalGroup (PeriodTorus L) p, ∃ m n : ℤ,
      v = (FundamentalGroup.fromPath (.mk ((γ 0).cast h h)))^m*(FundamentalGroup.fromPath (.mk ((γ 1).cast h h)))^n := by
  subst q
  exact hg

/-- Each transferred pair generates the approximating torus. The regular
covering lifts and integral generation are conclusions of smooth open
core transport. -/
theorem SmoothOpenTorusCoreMap.lifted_generators {A L : PeriodPair} {C : TorusGeneratingCoreModel A}
    (F : SmoothOpenTorusCoreMap C L) :
    ∃ D : SmoothGeneratingTorusCurves L, ∀ i s, periodTorusProjection L ((D.arc i).curve s) = F.trajectory i s := by
  classical
  let f := fun q : C.carrier => F.map q.1
  obtain ⟨_,_,_,hgen,_⟩ := C.ambient_detection f F.embedding
  obtain ⟨z,hz⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) (f C.base)
  have hc (i : Fin 2) : ContMDiff 𝓘(ℝ) 𝓘(ℝ,ℂ) 1 (F.trajectory i) := fun s =>
    ((F.smooth _ (C.trajectory_mem i s)).contMDiffAt
      (C.isOpen_carrier.mem_nhds (C.trajectory_mem i s))).comp s (markedTorusBasisTrajectory_smooth A i s)
  have he (i : Fin 2) (s : unitInterval) : F.trajectory i s = f (C.loop i s) :=
    congrArg F.map (C.projects i s).symm
  have hz₀ (i : Fin 2) : periodTorusProjection L z = F.trajectory i 0 :=
    hz.trans ((he i 0).trans (congrArg f (C.loop i).source)).symm
  choose arc h₀ h₁ hstart hproj using fun i => smooth_torus_curve_has_period_arc L (F.trajectory i) (hc i) z (hz₀ i)
    (fun s _ => F.avoids _ (C.trajectory_mem i s))
  let loop (i : Fin 2) : Path (periodTorusProjection L z) (periodTorusProjection L z) :=
    ((C.loop i).map F.embedding.continuous).cast hz hz
  refine ⟨⟨z,loop,arc,h₀,h₁,hstart,fun i s => (hproj i s).trans (he i s),?_⟩,hproj⟩
  exact torus_generators_cast hz (fun i => (C.loop i).map F.embedding.continuous) hgen

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.SmoothOpenTorusCoreMap.lifted_generators
