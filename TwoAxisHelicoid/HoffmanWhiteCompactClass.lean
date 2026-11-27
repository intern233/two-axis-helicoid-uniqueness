import TwoAxisHelicoid.UnmarkedNormalCutoffLimits
import TwoAxisHelicoid.PhysicalAppendixBCompactness

namespace TwoAxisHelicoid
open Set Filter Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- A genuine conformally parametrized punctured torus presenting the
same physical surface. This is part of the nonperiodic class definition
in Hoffman--White, pp. 767--768. -/
def HasPhysicalConformalTorus (s : OriginalSmoothHelicoid) : Prop :=
  ∃ (L : PeriodPair) (f : PuncturedPeriodTorus L ≃ₜ s.carrier) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ),
    (∀ q, s.position (f q)=Y q) ∧
    ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L Y) z)

theorem embedded_pitch_actual_conformal_type (W : PitchNormalizedBasicImmersion) (mem : W∈embeddedPitchFamily)
    (s : OriginalHelicoidRepresentative) (same : s.image=W.image) :
    HasPhysicalConformalTorus s.toOriginalSmoothHelicoid := by
  obtain ⟨f,pos⟩ := embedded_pitch_position_marking W mem s same
  exact ⟨_,f,fun q => WithLp.ofLp (W.torusPosition q.1),fun q => congrArg WithLp.ofLp (pos q),
    embedded_pitch_conformal_marking W mem⟩

/-- Membership facts about the fixed-axis symmetric genus-one
helicoid class. A positive screw period is allowed on any member.
For its nonperiodic members only their real, marked topology and
actual physical tangent bundle are needed. -/
structure FixedAxisHelicoidNormalClass (I : Type*) where
  normal : I → Set PhysicalPositionNormal
  member : ∀ s : OriginalHelicoidRepresentative, HasPhysicalConformalTorus s.toOriginalSmoothHelicoid →
    s.axes.pitch=1 → s.axes.horizontalPoint=0 → s.axes.horizontalDirection=1 →
    halfTurnX '' range s.position=range s.position → halfTurnZ '' range s.position=range s.position →
    ∃ m, normal m=s.unorientedNormals
  nonperiodic : ∀ m, (∀ h : ℝ, 0<h → unitHelicoidScrew h '' physicalNormalPositions (normal m)≠physicalNormalPositions (normal m)) →
    ∃ s : OriginalSmoothHelicoid, s.unorientedNormals=normal m

/-- The sequential compactness consequence in the proof of Theorem
7.1, p. 808, for each separate half-period cutoff. The returned class
member retains that cutoff. -/
def FixedAxisHelicoidNormalClass.compactCutoffs {I : Type*} (F : FixedAxisHelicoidNormalClass I) : Prop :=
  ∀ η : ℝ, Real.pi/2<η → ∀ a : ℕ → I, (∀ n, HasNoScrewBelow η (physicalNormalPositions (F.normal (a n)))) →
    ∃ (φ : ℕ → ℕ) (m : I), StrictMono φ ∧ LocalSpatialImageLimit (F.normal ∘ a ∘ φ) (F.normal m) ∧
      HasNoScrewBelow η (physicalNormalPositions (F.normal m))

/-- In a first-countable topology of smooth surfaces the published
topological compactness yields the required sequential formulation
as soon as positions and unoriented tangent planes converge locally. -/
theorem FixedAxisHelicoidNormalClass.compactCutoffs_of_topological {I : Type*} [TopologicalSpace I] [FirstCountableTopology I]
    (F : FixedAxisHelicoidNormalClass I)
    (compact : ∀ η : ℝ, Real.pi/2<η → IsCompact {m : I | HasNoScrewBelow η (physicalNormalPositions (F.normal m))})
    (smooth : ∀ (a : ℕ → I) m, Tendsto a atTop (𝓝 m) → LocalSpatialImageLimit (F.normal ∘ a) (F.normal m)) :
    F.compactCutoffs := by
  intro η pos a member
  obtain ⟨m,hm,φ,mono,conv⟩ := (compact η pos).isSeqCompact member
  exact ⟨φ,m,mono,smooth _ _ conv,hm⟩

/-- The limit handle in the flux argument requires only its real
smooth structure. Conformality of the initial surfaces is explicitly
verified on their own period tori before applying compactness. -/
theorem published_cutoff_original_handle_subsequence {I : Type*} (F : FixedAxisHelicoidNormalClass I) (hc : F.compactCutoffs)
    (x : ℕ → positiveUnitPitchFamily) :
    ∃ (φ : ℕ → ℕ) (s : OriginalSmoothHelicoid) (t : ℕ → OriginalHelicoidRepresentative),
      StrictMono φ ∧ (∀ n, (t n).image=(x (φ n)).1.image) ∧
        LocalSpatialImageLimit (fun n => (t n).unorientedNormals) s.unorientedNormals := by
  choose t ht using fun n => positive_pitch_actual_geometric_representative (x n).1 (x n).2
  have m (n : ℕ) : ∃ a, F.normal a=(t n).unorientedNormals := by
    obtain ⟨hit,pitch,h0,h1,_⟩ := ht n
    obtain ⟨ax,az⟩ := pitch_geometric_half_turns _ (x n).2.1 _ hit
    exact F.member _ (embedded_pitch_actual_conformal_type _ (x n).2.1 _ hit) pitch h0 h1 ax az
  choose a same using m
  have no (n : ℕ) (h : ℝ) (pos : 0<h) : unitHelicoidScrew h '' physicalNormalPositions (F.normal (a n))≠physicalNormalPositions (F.normal (a n)) := by
    rw [same,(t n).normal_positions]
    exact (t n).no_nonzero_screw_step (unitHelicoidScrew h) (d := 2*h) (by positivity) (unitHelicoidScrew_height h)
  obtain ⟨φ,m,mono,cv,_⟩ := hc (Real.pi/2+1) (by linarith) a (fun n h hp _ => no n h hp)
  have non (h : ℝ) (hp : 0<h) : unitHelicoidScrew h '' physicalNormalPositions (F.normal m)≠physicalNormalPositions (F.normal m) := by
    let η := max (Real.pi/2) h+1
    have bigger : Real.pi/2<η := by dsimp [η]; linarith [le_max_left (Real.pi/2) h]
    have above : h<η := by dsimp [η]; linarith [le_max_right (Real.pi/2) h]
    obtain ⟨ψ,j,hψ,limit,cut⟩ := hc η bigger (a ∘ φ) (fun n d dp _ => no (φ n) d dp)
    rw [(cv.subsequence hψ).unique limit]
    exact cut h hp above
  obtain ⟨s,agree⟩ := F.nonperiodic m non
  refine ⟨φ,s,t ∘ φ,mono,fun n => (ht (φ n)).1,?_⟩
  rw [agree]
  convert cv using 1
  funext n
  exact (same _).symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_pitch_actual_conformal_type
#print axioms TwoAxisHelicoid.FixedAxisHelicoidNormalClass.compactCutoffs_of_topological
#print axioms TwoAxisHelicoid.published_cutoff_original_handle_subsequence
