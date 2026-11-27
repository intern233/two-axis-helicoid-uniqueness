import TwoAxisHelicoid.SpatialNonperiodicCoreLimits
import TwoAxisHelicoid.CoreSheetPlaneConvergence

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- On an actual finite-sheet tube, convergence of positions and
unoriented tangent planes yields the marked nonperiodic compactness
conclusion used for the two generating loops in Appendix B. -/
theorem spatial_core_limit_from_positions_and_planes {S : Set PitchNormalizedBasicImmersion}
    (x : ℕ → S) (φ : ℕ → ℕ) (inc : StrictMono φ) (embedded : ∀ n, (x (φ n)).1∈embeddedPitchFamily)
    {A : PeriodPair} (C : TorusGeneratingCoreModel A) (G : ∀ n, SpatialCoreSheetCharts C (x (φ n)).1)
    (X N : ℂ → SurfaceEuclideanSpace) (signed : SurfaceEuclideanSpace → ℝ)
    (base : ∀ n (b : C.carrier) z, b.1=periodTorusProjection A z → (G n).position b=X z)
    (normal : ∀ n (b : C.carrier) z, b.1=periodTorusProjection A z → (G n).normal b=N z)
    (height : ∀ n (q : (G n).patch), (G n).signedHeight ((x (φ n)).1.torusPosition q.1)=signed ((x (φ n)).1.torusPosition q.1)) :
    let U := periodTorusProjection A ⁻¹' C.carrier
    let p := fun n (q : (G n).patch) => (G n).base ((x (φ n)).1.torusPosition q.1)
    (∀ z∈U, ContDiffAt ℝ 1 X z) → (∀ z∈U, ContDiffAt ℝ 1 N z) →
    (∀ z∈U, ‖N z‖=1 ∧ ∀ v, ⟪N z,fderiv ℝ X z v⟫=0) →
    (∀ z∈U, ContDiffAt ℝ 1 signed (X z)) → (∀ z∈U, signed (X z)=0) →
    ((∀ n, Function.Injective (p n)) → ∃ Z m : ℕ → ℂ → SurfaceEuclideanSpace,
      (∀ n (q : (G n).patch) z, (p n q).1=periodTorusProjection A z → Z n z=(x (φ n)).1.torusPosition q.1) ∧
      (∀ n z, z∈U → DifferentiableAt ℝ (Z n) z) ∧ (∀ n z, z∈U → DifferentiableAt ℝ signed (Z n z)) ∧
      (∀ n z, z∈U → ‖m n z‖=1 ∧ ∀ v, ⟪m n z,fderiv ℝ (Z n) z v⟫=0) ∧
      TendstoLocallyUniformlyOn Z X atTop U ∧
      TendstoLocallyUniformlyOn (fun n z => coreNormalDistance (m n z) (N z)) (fun _ => 0) atTop U) →
    HasLocalNormalGraphLimitSubsequence x := by
  dsimp only
  intro sx sn reference ss zero data
  apply spatial_charts_give_nonperiodic_core_limit x φ inc embedded C G X N signed base normal height sx sn ss zero
  intro inj
  obtain ⟨Z,m,pos,sz,ssz,perp,spatial,tilt⟩ := data inj
  let U := periodTorusProjection A ⁻¹' C.carrier
  have op : IsOpen U := C.isOpen_carrier.preimage QuotientAddGroup.continuous_mk
  let u := fun n => signed ∘ Z n
  have regular (n : ℕ) (z : ℂ) (hz : z∈U) : DifferentiableAt ℝ (u n) z := (ssz n z hz).comp z (sz n z hz)
  have small : TendstoLocallyUniformlyOn u (fun _ => 0) atTop U := by
    apply op.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
    intro z hz
    have lim := ((op.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp spatial) z hz)
    have v := ((sx z hz).continuousAt.tendsto.comp tendsto_snd).congr_uniformity lim
    have h := (ss z hz).continuousAt.tendsto.comp v
    rw [zero z hz] at h
    exact (tendsto_const_nhds.prodMk_nhds h).mono_right (nhds_le_uniformity _)
  have graph (n : ℕ) (z : ℂ) (hz : z∈U) : Z n z=X z+u n z • N z := by
    let D := (G n).toNormalCorePatch (embedded n)
    let b := (D.onto ⟨_,hz⟩).choose
    have hb : ((G n).base ((x (φ n)).1.torusPosition b.1)).1=periodTorusProjection A z :=
      congrArg Subtype.val (D.onto ⟨_,hz⟩).choose_spec
    have atz := pos n b z hb
    calc
      Z n z=(x (φ n)).1.torusPosition b.1 := atz
      _=_ := (G n).graph b
      _=X z+u n z • N z := by
        rw [base n _ z hb,normal n _ z hb,height n b]
        change X z+signed ((x (φ n)).1.torusPosition b.1) • N z=X z+signed (Z n z) • N z
        rw [atz]
  exact ⟨Z,pos,sz,ssz,spatial,(physical_plane_convergence_gives_core_derivative_convergence op X N Z m u
    sx sn regular graph reference perp small tilt).2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatial_core_limit_from_positions_and_planes
