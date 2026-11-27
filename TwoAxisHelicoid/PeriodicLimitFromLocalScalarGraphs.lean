import TwoAxisHelicoid.OpenTubeSliceTransport
import TwoAxisHelicoid.LocalFiniteHeightGraphSection
import TwoAxisHelicoid.ScrewPeriodicCoreCopies
import TwoAxisHelicoid.PeriodicSlabGeneratingCore
import TwoAxisHelicoid.ChartPunctureDiskHomeomorphism

namespace TwoAxisHelicoid
open Set Metric Topology

/-- Every compact part of the putative limit has one approximating
punctured torus in a genuine spatial tube. Only the actual height set
in each fiber is described by local finite scalar graphs. -/
def HasLocalTorusGraphApproximation {M : Type*} [TopologicalSpace M] (X : M → Fin 3 → ℝ)
    (T : ℕ → PeriodPair) (Y : (n : ℕ) → PuncturedPeriodTorus (T n) → Fin 3 → ℝ) : Prop :=
  ∀ K : Set M, IsCompact K → ∃ U : Set M, IsOpen U ∧ K⊆U ∧
    ∃ (n : ℕ) (tube : OpenPartialHomeomorph (U × ℝ) (Fin 3 → ℝ)),
      (∀ b : U, (b,0)∈tube.source ∧ tube (b,0)=X b.1) ∧
      HasLocalFiniteHeightGraphs {q : U × ℝ | q∈tube.source ∧ tube q∈range (Y n)}

/-- Local scalar graphs in spatial tubes give an open embedding of a
neighborhood of each compact subset into one actual approximating
torus. This also works for compact subsets with more than one component. -/
theorem local_torus_height_graphs_carry_compact_patches {M : Type*} [TopologicalSpace M] [T2Space M]
    (X : M → Fin 3 → ℝ) (T : ℕ → PeriodPair) (Y : (n : ℕ) → PuncturedPeriodTorus (T n) → Fin 3 → ℝ)
    (emb : ∀ n, IsEmbedding (Y n)) (graphs : HasLocalTorusGraphApproximation X T Y)
    (K : Set M) (compact : IsCompact K) :
    ∃ U : Set M, IsOpen U ∧ K⊆U ∧ ∃ (n : ℕ) (j : U → PeriodTorus (T n)), IsOpenEmbedding j := by
  obtain ⟨U,op,inside,n,e,_,sheets⟩ := graphs K compact
  let A := {q : U × ℝ | q∈e.source ∧ e q∈range (Y n)}
  obtain ⟨s,sectionOpen,_,_⟩ := lowest_open_section_of_local_height_graphs A sheets
  obtain ⟨g,patchOpen,_⟩ := open_tube_slice_embeds_in_surface e (Y n) (emb n)
  let _ : T1Space (PeriodTorus (T n)) := QuotientAddGroup.t1Space_iff.mpr (T n).isClosed_lattice
  have puncture : IsOpenEmbedding (Subtype.val : PuncturedPeriodTorus (T n) → PeriodTorus (T n)) :=
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal
  exact ⟨U,op,inside,n,Subtype.val ∘ g ∘ s,puncture.comp (patchOpen.comp sectionOpen)⟩

/-- One open punctured-torus patch in a horizontal slab supplies the
compact handle used to rule out screw-periodic limits. -/
theorem screw_periodic_punctured_patch_excluded_by_local_height_graphs {M : Type*}
    [TopologicalSpace M] [T2Space M] (X : M → Fin 3 → ℝ) (embedded : IsEmbedding X)
    (T : ℕ → PeriodPair) (Y : (n : ℕ) → PuncturedPeriodTorus (T n) → Fin 3 → ℝ)
    (emb : ∀ n, IsEmbedding (Y n)) (graphs : HasLocalTorusGraphApproximation X T Y)
    (A : PeriodPair) {h : ℝ}
    (slabChart : PuncturedPeriodTorus A → {p : M // X p 2∈Ioo (-h) h}) (patch : IsOpenEmbedding slabChart)
    (S : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) {d : ℝ} (step : d≠0) (moves : ∀ v, S v 2=v 2+d) :
    S '' range X≠range X := by
  let j := Subtype.val ∘ slabChart
  have os : IsOpen {p : M | X p 2∈Ioo (-h) h} := isOpen_Ioo.preimage ((continuous_apply _).comp embedded.continuous)
  obtain ⟨C,f,K,hf,hK,cover⟩ := punctured_torus_patch_carries_compact_core A j
    (os.isOpenEmbedding_subtypeVal.comp patch)
  intro symmetry
  apply screw_periodic_core_excludes_local_torus_embeddings X embedded S step moves symmetry C f hf K hK cover
  intro B bounded
  obtain ⟨U,op,inside,n,i,opened⟩ := local_torus_height_graphs_carry_compact_patches X T Y emb graphs B bounded
  exact ⟨U,op,inside,T n,i,opened⟩

/-- The periodic alternative at one fixed cutoff is impossible from
actual local scalar graphs of genus-one approximants. The limiting
physical slab is a torus with a closed chart disk removed. -/
theorem screw_periodic_disk_slab_excluded_by_local_height_graphs {M : Type*}
    [TopologicalSpace M] [T2Space M] (X : M → Fin 3 → ℝ) (embedded : IsEmbedding X)
    (T : ℕ → PeriodPair) (Y : (n : ℕ) → PuncturedPeriodTorus (T n) → Fin 3 → ℝ)
    (emb : ∀ n, IsEmbedding (Y n)) (graphs : HasLocalTorusGraphApproximation X T Y)
    (A : PeriodPair) {h r : ℝ} (e : OpenPartialHomeomorph (PeriodTorus A) ℂ)
    (center : (0:PeriodTorus A)∈e.source) (pos : 0<r) (buffer : closedBall (e 0) (2*r)⊆e.target)
    (slab : {p : PeriodTorus A // p∉e.symm '' closedBall (e 0) r} ≃ₜ {p : M // X p 2∈Ioo (-h) h})
    (S : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) {d : ℝ} (step : d≠0) (moves : ∀ v, S v 2=v 2+d) :
    S '' range X≠range X := by
  let _ : T1Space (PeriodTorus A) := QuotientAddGroup.t1Space_iff.mpr A.isClosed_lattice
  obtain ⟨puncture⟩ := chart_puncture_closed_disk_homeomorphism e center pos buffer
  let slabChart := puncture.trans slab
  exact screw_periodic_punctured_patch_excluded_by_local_height_graphs X embedded T Y emb graphs A
    slabChart slabChart.isOpenEmbedding S step moves

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.local_torus_height_graphs_carry_compact_patches
#print axioms TwoAxisHelicoid.screw_periodic_punctured_patch_excluded_by_local_height_graphs
#print axioms TwoAxisHelicoid.screw_periodic_disk_slab_excluded_by_local_height_graphs
