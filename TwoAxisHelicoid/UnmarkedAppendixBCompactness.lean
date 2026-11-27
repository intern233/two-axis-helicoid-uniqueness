import TwoAxisHelicoid.UnmarkedPitchCoreTransport
import TwoAxisHelicoid.NormalCutoffCompactImages
import TwoAxisHelicoid.OriginalAnnularEndConsequences
import TwoAxisHelicoid.PositionalAppendixBCompactness

namespace TwoAxisHelicoid
open Set Filter Metric Topology TopologicalSpace
open scoped Topology ContDiff Manifold

/-- The normalized Hoffman--White class evaluated in actual point and
normal coordinates. The compactness clause allows periodic members at
every finite cutoff, and does not specify a torus marking, multiplicity,
sheet projection or any derivative on a transported curve. -/
def UnmarkedUnitPitchCutoffCompactness : Prop :=
  ∃ family : Set (Set PhysicalPositionNormal),
    (∀ U∈family, IsClosed U ∧ U.Nonempty) ∧
    (∀ s : OriginalHelicoidRepresentative, s.axes.pitch=1 → s.axes.horizontalPoint=0 →
      s.axes.horizontalDirection=1 → halfTurnX '' range s.position=range s.position →
      halfTurnZ '' range s.position=range s.position → s.unorientedNormals∈family) ∧
    (∀ U∈family, (∀ h : ℝ, 0<h → unitHelicoidScrew h '' physicalNormalPositions U≠physicalNormalPositions U) →
      ∃ s : OriginalHelicoidRepresentative, s.unorientedNormals=U) ∧
    ∀ η : ℝ, Real.pi/2<η → IsCompact
      (denseDistanceProfile '' {U | U∈family ∧ HasNoScrewBelow η (physicalNormalPositions U)})

/-- The compactness cutoff extracts a single original nonperiodic
handle as point--normal limit. This precedes any comparison of period
data or any use of uniformization of the limiting handle. -/
theorem unmarked_unit_pitch_subsequence (hwv : UnmarkedUnitPitchCutoffCompactness)
    (x : ℕ → positiveUnitPitchFamily) :
    ∃ (φ : ℕ → ℕ) (s : OriginalHelicoidRepresentative) (moving : ℕ → OriginalHelicoidRepresentative),
      StrictMono φ ∧ (∀ n, (moving n).image=(x (φ n)).1.image) ∧
      LocalSpatialImageLimit (fun n => (moving n).unorientedNormals) s.unorientedNormals := by
  obtain ⟨family,regular,member,identify,compact⟩ := hwv
  choose t ht using fun n => positive_pitch_actual_geometric_representative (x n).1 (x n).2
  let S := fun n => (t n).unorientedNormals
  have inclass (n : ℕ) : S n∈family := by
    obtain ⟨eq,pitch,h0,h1,_⟩ := ht n
    obtain ⟨ax,az⟩ := pitch_geometric_half_turns _ (x n).2.1 _ eq
    exact member _ pitch h0 h1 ax az
  have no (n : ℕ) (h : ℝ) (hp : 0<h) :
      unitHelicoidScrew h '' physicalNormalPositions (S n)≠physicalNormalPositions (S n) := by
    rw [show physicalNormalPositions (S n)=range (t n).position from (t n).normal_positions]
    exact (t n).no_nonzero_screw_step (unitHelicoidScrew h) (d := 2*h) (by positivity) (unitHelicoidScrew_height h)
  obtain ⟨φ,K,hφ,hK,cv,non⟩ := compact_normal_cutoffs_preserve_nonperiodicity family regular compact S inclass no
  obtain ⟨s,hs⟩ := identify K hK non
  exact ⟨φ,s,t ∘ φ,hφ,fun n => (ht (φ n)).1,hs.symm ▸ cv⟩

/-- Only the limiting original handle needs a regular torus coordinate.
The compactness theorem supplies none of the curves or smooth core maps
used in the integral flux bound. -/
theorem unmarked_compactness_gives_core_transport (hwv : UnmarkedUnitPitchCutoffCompactness)
    (mark : ∀ s : OriginalHelicoidRepresentative, ∃ (A : PeriodPair) (f : s.carrier ≃ₜ PuncturedPeriodTorus A)
      (Y : PeriodTorus A → Fin 3 → ℝ), (∀ q, Y (f q).1=s.position q) ∧
      ∀ z∉A.lattice, ContDiffAt ℝ ∞ (Y ∘ periodTorusProjection A) z ∧ Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection A) z)) :
    HasLocalC1CoreCompactness positiveUnitPitchFamily := by
  intro x
  obtain ⟨φ,s,t,hφ,hit,cv⟩ := unmarked_unit_pitch_subsequence hwv x
  obtain ⟨A,f,Y,loc,regular⟩ := mark s
  obtain ⟨C⟩ := exists_torus_generating_core_model A
  obtain ⟨k,F,h⟩ := unmarked_pitch_core_transport s.toOriginalSmoothHelicoid f Y loc regular
    (fun n => (x (φ n)).1) (fun n => (x (φ n)).2.1) t hit cv C
  exact ⟨fun n => φ (n+k),hφ.comp (strictMono_id.add_const k),A,C,F,coordinateToEuclidean ∘ Y ∘ periodTorusProjection A,h⟩

/-- B.1 and B.2 on the normalized embedded data, via the original
compactness and flux argument. Neither horizontal box signs nor a
period classification of the limiting immersion enter the proof. -/
theorem unmarked_unit_pitch_flux_gap_and_finiteness (hwv : UnmarkedUnitPitchCutoffCompactness)
    (ann : AnnularRiemannSurfaceUniformization.{0}) (form : GenusOneHasHolomorphicDifferential.{0}) :
    (∃ ε : ℝ, 0<ε ∧ ∀ W∈positiveUnitPitchFamily, ε≤W.t) ∧
      ((fun W : PitchNormalizedBasicImmersion => Quotient.mk (spatialSimilaritySetoid _) W.image) '' positiveUnitPitchFamily).Finite := by
  apply local_C1_core_compactness_gives_gap_and_finite_images
  apply unmarked_compactness_gives_core_transport hwv
  intro s
  have U := genus_one_period_uniformization_from_canonical_divisor (genus_one_canonical_divisor_of_one_section form) s.modelTorus
  obtain ⟨P,_⟩ := original_annular_end_pole_model_and_index s ann
  obtain ⟨_,_,_,A,f,Y,_,_,pos,_,_,reg,_,_⟩ := original_smooth_surface_published_poles_to_torus
    s.toOriginalSmoothHelicoid U P.some s.positional.1
  refine ⟨A,f,Y,pos,fun z nz => ⟨(analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt ((reg z nz).1 j)).contDiffAt,
    (reg z nz).2.2⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unmarked_unit_pitch_subsequence
#print axioms TwoAxisHelicoid.unmarked_compactness_gives_core_transport
#print axioms TwoAxisHelicoid.unmarked_unit_pitch_flux_gap_and_finiteness
