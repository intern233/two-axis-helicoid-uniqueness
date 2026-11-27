import TwoAxisHelicoid.SpatialCoreSheetCharts
import TwoAxisHelicoid.MarkedCoreTubeHeightDecay

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff

/-- C¹ convergence in Euclidean positions gives precisely the
nonperiodic alternative of the compact-core theorem. Local finite sheet
charts may initially have several sheets. The pulled positions are used
only once their uniqueness over the base has been established. -/
theorem spatial_charts_give_nonperiodic_core_limit {S : Set PitchNormalizedBasicImmersion}
    (x : ℕ → S) (φ : ℕ → ℕ) (hφ : StrictMono φ) (hW : ∀ n, (x (φ n)).1 ∈ embeddedPitchFamily)
    {A : PeriodPair} (C : TorusGeneratingCoreModel A) (G : ∀ n, SpatialCoreSheetCharts C (x (φ n)).1)
    (X N : ℂ → EuclideanSpace ℝ (Fin 3)) (signed : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Gpos : ∀ n (b : C.carrier) z, b.1 = periodTorusProjection A z → (G n).position b = X z)
    (Gnorm : ∀ n (b : C.carrier) z, b.1 = periodTorusProjection A z → (G n).normal b = N z)
    (Gheight : ∀ n (q : (G n).patch), (G n).signedHeight ((x (φ n)).1.torusPosition q.1) = signed ((x (φ n)).1.torusPosition q.1)) :
    let U := periodTorusProjection A ⁻¹' C.carrier
    let p := fun n (q : (G n).patch) => (G n).base ((x (φ n)).1.torusPosition q.1)
    (∀ z ∈ U, ContDiffAt ℝ 1 X z) → (∀ z ∈ U, ContDiffAt ℝ 1 N z) →
    (∀ z ∈ U, ContDiffAt ℝ 1 signed (X z)) → (∀ z ∈ U, signed (X z) = 0) →
    ((∀ n, Function.Injective (p n)) → ∃ Z : ℕ → ℂ → EuclideanSpace ℝ (Fin 3),
      (∀ n (q : (G n).patch) z, (p n q).1 = periodTorusProjection A z → Z n z = (x (φ n)).1.torusPosition q.1) ∧
      (∀ n z, z ∈ U → DifferentiableAt ℝ (Z n) z) ∧ (∀ n z, z ∈ U → DifferentiableAt ℝ signed (Z n z)) ∧
      TendstoLocallyUniformlyOn Z X atTop U ∧ TendstoLocallyUniformlyOn (fun n => fderiv ℝ (Z n)) (fderiv ℝ X) atTop U) →
    HasLocalNormalGraphLimitSubsequence x := by
  dsimp only
  intro hX hN hs hzero spatial
  let W := fun n => (x (φ n)).1
  let D := fun n => (G n).toNormalCorePatch (hW n)
  have inj (n : ℕ) : Function.Injective (D n).project := by
    obtain ⟨F,hF⟩ := normal_cover_gives_smooth_open_core C Subtype.val
      (D n).isOpen_patch.isOpenEmbedding_subtypeVal (D n).avoids (D n).proper (D n).localHomeomorph
      (D n).onto (D n).continuous_height (D n).separates (D n).inverseGerms
    intro a b eq
    apply Subtype.ext
    rw [← hF a,← hF b,eq]
  obtain ⟨Z,hpos,hZ,hδ,hv,hd⟩ := spatial inj
  obtain ⟨hreg,h₀,h₁⟩ := marked_core_plane_heights_decay C W D X Z signed hpos Gheight hX hZ hs hδ hzero hv hd
  refine ⟨φ,hφ,Or.inr ⟨A,C,D,X,N,hX,hN,fun n _ => hreg n,?_,fun _ => ⟨h₀,h₁⟩⟩⟩
  intro n b z hb
  exact ((G n).graph b).trans (congrArg₂ (· + ·) (Gpos n _ z hb)
    (congrArg ((G n).signedHeight ((x (φ n)).1.torusPosition b.1) • ·) (Gnorm n _ z hb)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatial_charts_give_nonperiodic_core_limit
