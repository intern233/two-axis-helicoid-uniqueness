import TwoAxisHelicoid.PeriodicLimitFromPointNormals
import TwoAxisHelicoid.SingleCutoffFluxGap

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology

/-- The handle carried outside a closed disk in a marked torus. -/
def TorusDiskComplementHandleProperty : Prop :=
  ∀ (L : PeriodPair) (u : C(Metric.closedBall (0:ℂ) 1,PeriodTorus L)), IsEmbedding u →
    ∃ f : PuncturedPeriodTorus L → {p : PeriodTorus L // p∉range u}, IsOpenEmbedding f

/-- The periodic class member of Hoffman–White, Theorems 6.2 and 7.1.
Its open fundamental slab is a torus with a topological closed disk
deleted. The normal pairs belong to the same actual spatial surface. -/
structure PeriodicSlabNormalMember (P : Set PhysicalPositionNormal) where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [separated : T2Space carrier]
  [charts : ChartedSpace ℂ carrier]
  position : carrier → Fin 3 → ℝ
  closed : IsClosedEmbedding position
  unitNormal : carrier → SurfaceEuclideanSpace
  regular : RegularSurfaceNormalInCharts (coordinateToEuclidean ∘ position) unitNormal
  measured : P=unorientedSurfaceNormals (coordinateToEuclidean ∘ position) unitNormal
  halfPeriod : ℝ
  positive : 0<halfPeriod
  periodic : unitHelicoidScrew halfPeriod '' range position=range position
  torus : PeriodPair
  disk : C(closedBall (0:ℂ) 1,PeriodTorus torus)
  embeddedDisk : IsEmbedding disk
  slab : {q : PeriodTorus torus // q∉range disk} ≃ₜ {q : carrier // position q 2∈Ioo (-halfPeriod) halfPeriod}

attribute [instance] PeriodicSlabNormalMember.topology PeriodicSlabNormalMember.separated PeriodicSlabNormalMember.charts

/-- A regular screw-periodic fundamental slab carrying a torus minus a disk
cannot be the local point-normal limit of embedded punctured tori. -/
theorem PeriodicSlabNormalMember.not_local_limit {L : Set PhysicalPositionNormal}
    (P : PeriodicSlabNormalMember L) (diskTop : TorusDiskComplementHandleProperty)
    (moving : ℕ → OriginalSmoothHelicoid) (limit : LocalSpatialImageLimit (fun n => (moving n).unorientedNormals) L) :
    False := by
  obtain ⟨g,og⟩ := diskTop P.torus P.disk P.embeddedDisk
  let f := Subtype.val ∘ P.slab ∘ g
  have op : IsOpen {q : P.carrier | P.position q 2∈Ioo (-P.halfPeriod) P.halfPeriod} :=
    isOpen_Ioo.preimage ((continuous_apply _).comp P.closed.continuous)
  obtain ⟨C,j,K,oj,kc,carried⟩ := punctured_torus_patch_carries_compact_core P.torus f
    (op.isOpenEmbedding_subtypeVal.comp (P.slab.isOpenEmbedding.comp og))
  have cv : LocalSpatialImageLimit (fun n => (moving n).unorientedNormals)
      (unorientedSurfaceNormals (coordinateToEuclidean ∘ P.position) P.unitNormal) := P.measured ▸ limit
  exact screw_periodic_handle_excluded_by_point_normal_convergence P.position P.closed P.unitNormal P.regular
    moving cv C j oj K kc carried (unitHelicoidScrew P.halfPeriod)
    (d:=2*P.halfPeriod) (mul_ne_zero two_ne_zero P.positive.ne') (unitHelicoidScrew_height P.halfPeriod) P.periodic

/-- Once a single cutoff returns a member and its point-normal limit,
the embedded handle rules out every periodic alternative. -/
theorem point_normal_cutoff_subsequence_gives_handle_limit {I : Type*}
    (diskTop : TorusDiskComplementHandleProperty) (η : ℝ) (family : FixedAxisHelicoidNormalClass I)
    (extract : ∀ a : ℕ → I, (∀ n, HasNoScrewBelow η (physicalNormalPositions (family.normal (a n)))) →
      ∃ m, HasNoScrewBelow η (physicalNormalPositions (family.normal m)) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ LocalSpatialImageLimit (family.normal ∘ a ∘ φ) (family.normal m))
    (slab : ∀ m, HasNoScrewBelow η (physicalNormalPositions (family.normal m)) →
      (∃ h : ℝ, 0<h ∧ unitHelicoidScrew h '' physicalNormalPositions (family.normal m)=physicalNormalPositions (family.normal m)) →
      Nonempty (PeriodicSlabNormalMember (family.normal m))) :
    FixedCutoffHandleCompactness η := by
  intro t norm
  choose a same using fun n => family.member (t n) (norm n).1 (norm n).2.1 (norm n).2.2.1
    (norm n).2.2.2.1 (norm n).2.2.2.2.1 (norm n).2.2.2.2.2
  have member (n : ℕ) : HasNoScrewBelow η (physicalNormalPositions (family.normal (a n))) := by
    rw [same,(t n).normal_positions]
    intro h hp _
    exact (t n).no_nonzero_screw_step (unitHelicoidScrew h) (d:=2*h) (by positivity) (unitHelicoidScrew_height h)
  obtain ⟨m,hm,φ,inc,limit⟩ := extract a member
  have transported : LocalSpatialImageLimit (fun n => (t (φ n)).unorientedNormals) (family.normal m) := by
    simpa only [Function.comp_def,same] using limit
  have nonper (h : ℝ) (pos : 0<h) :
      unitHelicoidScrew h '' physicalNormalPositions (family.normal m)≠physicalNormalPositions (family.normal m) := by
    intro eq
    obtain ⟨P⟩ := slab m hm ⟨h,pos,eq⟩
    exact P.not_local_limit diskTop (fun n => (t (φ n)).toOriginalSmoothHelicoid) transported
  obtain ⟨s,eq⟩ := family.nonperiodic m nonper
  exact ⟨φ,inc,Or.inl ⟨s,by rw [eq]; exact transported⟩⟩

/-- The topological compactness of one class at one cutoff and convergence
of unoriented tangent planes imply that the length-transport argument
always reaches a nonperiodic member. -/
theorem one_compact_cutoff_gives_handle_limit {I : Type*} [TopologicalSpace I] [FirstCountableTopology I]
    (diskTop : TorusDiskComplementHandleProperty) (η : ℝ) (family : FixedAxisHelicoidNormalClass I)
    (compact : IsCompact {m : I | HasNoScrewBelow η (physicalNormalPositions (family.normal m))})
    (smooth : ∀ (a : ℕ → I) m, Tendsto a atTop (𝓝 m) → LocalSpatialImageLimit (family.normal ∘ a) (family.normal m))
    (slab : ∀ m, HasNoScrewBelow η (physicalNormalPositions (family.normal m)) →
      (∃ h : ℝ, 0<h ∧ unitHelicoidScrew h '' physicalNormalPositions (family.normal m)=physicalNormalPositions (family.normal m)) →
      Nonempty (PeriodicSlabNormalMember (family.normal m))) :
    FixedCutoffHandleCompactness η := by
  apply point_normal_cutoff_subsequence_gives_handle_limit diskTop η family _ slab
  intro a inside
  obtain ⟨m,hm,φ,mono,limit⟩ := compact.isSeqCompact inside
  exact ⟨m,hm,φ,mono,smooth _ _ limit⟩

/-- The two conclusions of Appendix B by the manuscript's single-cutoff
geometric argument, with point-normal convergence as the only convergence
input and the actual periodic fundamental slab from the class theorem. -/
theorem original_appendix_B_from_one_compact_normal_class {I : Type*} [TopologicalSpace I] [FirstCountableTopology I]
    (diskTop : TorusDiskComplementHandleProperty) (η : ℝ) (eta : Real.pi/2<η) (family : FixedAxisHelicoidNormalClass I)
    (compact : IsCompact {m : I | HasNoScrewBelow η (physicalNormalPositions (family.normal m))})
    (smooth : ∀ (a : ℕ → I) m, Tendsto a atTop (𝓝 m) → LocalSpatialImageLimit (family.normal ∘ a) (family.normal m))
    (slab : ∀ m, HasNoScrewBelow η (physicalNormalPositions (family.normal m)) →
      (∃ h : ℝ, 0<h ∧ unitHelicoidScrew h '' physicalNormalPositions (family.normal m)=physicalNormalPositions (family.normal m)) →
      Nonempty (PeriodicSlabNormalMember (family.normal m))) :
    HasSubsequentialSmoothGeneratingCurves positiveUnitPitchFamily ∧
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧
      ∀ s : OriginalHelicoidRepresentative, ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite :=
  original_graph_appendix_B_from_one_fixed_cutoff η eta (one_compact_cutoff_gives_handle_limit diskTop η family compact smooth slab)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.PeriodicSlabNormalMember.not_local_limit
#print axioms TwoAxisHelicoid.point_normal_cutoff_subsequence_gives_handle_limit
#print axioms TwoAxisHelicoid.one_compact_cutoff_gives_handle_limit
#print axioms TwoAxisHelicoid.original_appendix_B_from_one_compact_normal_class
