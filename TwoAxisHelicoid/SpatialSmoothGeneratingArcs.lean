import TwoAxisHelicoid.HomotopicSmoothTorusGenerators

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff Manifold

/-- An open physical marking transports smooth representatives of a
topological generating pair to actual plane arcs on the normalized
surface. Their Euclidean trajectories agree at every real parameter. -/
theorem generating_arcs_of_smooth_spatial_loops {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    {V : Type*} [TopologicalSpace V] (e : V ≃ₜ C.carrier)
    (W : PitchNormalizedBasicImmersion) (mem : W∈embeddedPitchFamily)
    (σ : V → PuncturedPeriodTorus (rhombicPeriodPair W.t W.ht)) (openσ : IsOpenEmbedding σ)
    (g : Fin 2 → ℝ → V) (cg : ∀ i, Continuous (g i))
    (c : Fin 2 → Path (e.symm C.base) (e.symm C.base))
    (hom : ∀ i, ((C.loop i).map e.symm.continuous).Homotopic (c i))
    (val : ∀ i (t : unitInterval), c i t=g i t)
    (F : V → EuclideanSpace ℝ (Fin 3)) (pos : ∀ q, W.torusPosition (σ q).1=F q)
    (sm : ∀ i, ContDiff ℝ 1 (F ∘ g i)) :
    ∃ D : SmoothGeneratingTorusCurves (rhombicPeriodPair W.t W.ht), ∀ i,
      coordinateToEuclidean ∘ W.position ∘ (D.arc i).curve=F ∘ g i := by
  let L := rhombicPeriodPair W.t W.ht
  let j₀ := (Subtype.val : PuncturedPeriodTorus L → PeriodTorus L) ∘ σ
  let j := j₀ ∘ e.symm
  have oj : IsOpenEmbedding j₀ := isOpen_ne.isOpenEmbedding_subtypeVal.comp openσ
  have embed : IsOpenEmbedding j := oj.comp e.symm.isOpenEmbedding
  let d := fun i => (c i).map oj.continuous
  have hd (i : Fin 2) : ((C.loop i).map embed.continuous).Homotopic (d i) :=
    (hom i).map (⟨j₀,oj.continuous⟩ : C(V,PeriodTorus L))
  let p := fun i => j₀ ∘ g i
  have smooth (i : Fin 2) : ContMDiff 𝓘(ℝ) 𝓘(ℝ,ℂ) 1 (p i) := by
    apply embedded_pitch_smooth_curve_of_position W mem (σ ∘ g i) (openσ.continuous.comp (cg i))
    convert sm i using 1
    funext t
    exact pos _
  obtain ⟨D,proj⟩ := smooth_curves_of_core_homotopies C j embed d hd p smooth
    (fun i t => congrArg j₀ (val i t).symm) (fun i t => (σ (g i t)).2)
  refine ⟨D,fun i => funext (fun t => ?_)⟩
  have away : (D.arc i).curve t∉L.lattice := fun h => (σ (g i t)).2 ((proj i t).symm.trans ((periodTorusProjection_eq_zero _ _).mpr h))
  exact ((W.torusPosition_projection _ away).symm.trans (congrArg W.torusPosition (proj i t))).trans (pos _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.generating_arcs_of_smooth_spatial_loops
