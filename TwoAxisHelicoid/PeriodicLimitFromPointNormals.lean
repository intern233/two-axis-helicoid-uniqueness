import TwoAxisHelicoid.OpenHandleCoreNormalConvergence
import TwoAxisHelicoid.ScrewPeriodicCoreCopies

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- A screw-periodic surface with a compactly carried open handle cannot be
a local limit of the point-normal sets of embedded once-punctured tori.
Two widely separated translates of its handle give disjoint open handle
patches on one and the same moving torus. -/
theorem screw_periodic_handle_excluded_by_point_normal_convergence {B : Type*}
    [TopologicalSpace B] [T2Space B] [ChartedSpace ℂ B]
    (X : B → Fin 3 → ℝ) (closed : IsClosedEmbedding X) (N : B → SurfaceEuclideanSpace)
    (normal : RegularSurfaceNormalInCharts (coordinateToEuclidean ∘ X) N) (moving : ℕ → OriginalSmoothHelicoid)
    (conv : LocalSpatialImageLimit (fun n => (moving n).unorientedNormals)
      (unorientedSurfaceNormals (coordinateToEuclidean ∘ X) N))
    {A : PeriodPair} (C : TorusGeneratingCoreModel A) (f : C.carrier → B) (op : IsOpenEmbedding f)
    (K : Set B) (compact : IsCompact K) (inside : range f⊆K)
    (S : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) {d : ℝ} (non : d≠0) (step : ∀ v, S v 2=v 2+d) :
    S '' range X≠range X := by
  intro symm
  obtain ⟨F,L,core,apart⟩ := screw_period_repeats_compact_core X closed.isEmbedding S non step symm C f op K compact inside
  have ce : IsClosedEmbedding (coordinateToEuclidean ∘ X) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp closed
  have sheets (i : ℕ) := local_normal_limit_transports_open_handle _ N ce normal moving conv C (F i)
    (core i).1 (L i) (core i).2.1 (core i).2.2 (1/4) (by norm_num)
  obtain ⟨n,⟨j,oj,closej⟩,k,ok,closek⟩ := ((sheets 0).and (sheets 1)).exists
  let T := (moving n).modelTorus
  let _ : T1Space (PeriodTorus T) := QuotientAddGroup.t1Space_iff.mpr T.isClosed_lattice
  let u := (Subtype.val : PuncturedPeriodTorus T → PeriodTorus T) ∘ (moving n).topologicalType
  have opened : IsOpenEmbedding u := isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp
    (moving n).topologicalType.isOpenEmbedding
  apply disjoint_genus_one_cores_impossible C C (u ∘ j) (u ∘ k) (opened.comp oj) (opened.comp ok)
  apply Set.disjoint_left.mpr
  rintro _ ⟨b,rfl⟩ ⟨a,eq⟩
  have same : k a=j b := opened.injective eq
  have p := (PiLp.norm_apply_le ((moving n).euclideanPosition (j b)-coordinateToEuclidean (X (F 0 b))) 2).trans_lt (closej b)
  have q := (PiLp.norm_apply_le ((moving n).euclideanPosition (k a)-coordinateToEuclidean (X (F 1 a))) 2).trans_lt (closek a)
  change ‖(moving n).position (j b) 2-X (F 0 b) 2‖<(1/4:ℝ) at p
  change ‖(moving n).position (k a) 2-X (F 1 a) 2‖<(1/4:ℝ) at q
  rw [Real.norm_eq_abs] at p
  rw [Real.norm_eq_abs,same] at q
  obtain ⟨p1,p2⟩ := abs_lt.mp p
  obtain ⟨q1,q2⟩ := abs_lt.mp q
  have far := apart 0 1 (by decide) _ ((core 0).2.2 (mem_range_self b)) _ ((core 1).2.2 (mem_range_self a))
  exact far.not_ge (abs_le.mpr ⟨by linarith,by linarith⟩)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.screw_periodic_handle_excluded_by_point_normal_convergence
