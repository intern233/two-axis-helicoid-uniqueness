import TwoAxisHelicoid.CertifiedCentralHalfPeriods
import TwoAxisHelicoid.CertifiedAxisCollisionCore

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ComplexConjugate

/-- Two regular points on the two central saddle arcs, on opposite
sides of the vertical axis. -/
noncomputable def rhombicCentralMark {t : ℝ} (ht : 0<t) (positive : Bool) :
    PuncturedPeriodTorus (rhombicPeriodPair t ht) :=
  let z : ℂ := (1+I*t)/2
  let w := if positive then z else -conj z
  ⟨periodTorusProjection _ w,fun e => rhombic_horizontal_strip_not_mem ht
    (z:=w) (by
      have h : z.im=t/2 := by simp [z,div_ofNat_im]
      have k : (-conj z).im=z.im := by simp
      have v : w.im=t/2 := by cases positive <;> first | exact h | exact k.trans h
      change w.im∈Ioo 0 t
      rw [v]
      constructor <;> linarith)
    ((periodTorusProjection_eq_zero _ _).mp e)⟩

/-- The certified map is jointly injective on both *complete* axes and
both central half periods. Moreover every possible double point has a
preimage in a compact set disjoint from their union. -/
theorem certified_embedding_away_from_axes_and_half_periods :
    let p := certifiedClosedParameters
    let A := rhombicMarkedAxes p.t p.height_pos ∪
      {rhombicCentralMark p.height_pos true,rhombicCentralMark p.height_pos false}
    InjOn certifiedTorusImmersion A ∧
      ∃ B K : Set (PuncturedPeriodTorus certifiedPeriodPair), IsCompact B ∧ IsCompact K ∧
        B⊆K ∧ Disjoint A B ∧ InjOn certifiedTorusImmersion Bᶜ ∧
        (IsClosedEmbedding certifiedTorusImmersion ↔ ∀ x∈B, ∀ y∈K, certifiedTorusImmersion x=certifiedTorusImmersion y → x=y) := by
  intro p A
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  let a := rhombicCentralMark p.height_pos true
  let b := rhombicCentralMark p.height_pos false
  let axes := rhombicMarkedAxes p.t p.height_pos
  let z : ℂ := (1+I*p.t)/2
  have diff : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun w hw =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 w hw).1
  have value {u : PuncturedPeriodTorus certifiedPeriodPair} {w : ℂ}
      (e : periodTorusProjection certifiedPeriodPair w=u.1) :
      certifiedTorusImmersion u 1=X w 1 := by
    change actualTorusImmersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed u.1 1=_
    rw [← e]
    rfl
  have ax (x) (hx : x∈axes) : certifiedTorusImmersion x 1=X 1 1 := by
    obtain ⟨w,mem,eq⟩ := rhombicMarkedAxes_regular_representatives p.height_pos hx
    rw [value eq]
    rcases mem with ⟨u,hu,rfl⟩|⟨u,hu,rfl⟩
    · exact (actual_primitive_horizontal_line p.height_pos diff hu).1
    · exact (actual_primitive_vertical_line p.height_pos diff hu).2
  have pa : certifiedTorusImmersion a 1=X z 1 := value rfl
  have pb : certifiedTorusImmersion b 1=X (-conj z) 1 := value rfl
  obtain ⟨ha,hb,_⟩ := certified_central_half_periods_separated
  change 1/2<X z 1-X 1 1 at ha
  change 1/2<X 1 1-X (-conj z) 1 at hb
  have disA (u) (hu : u∈axes) : certifiedTorusImmersion u≠certifiedTorusImmersion a := by
    intro e
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) e
    change certifiedTorusImmersion u 1=certifiedTorusImmersion a 1 at h
    rw [ax _ hu,pa] at h
    linarith
  have disB (u) (hu : u∈axes) : certifiedTorusImmersion u≠certifiedTorusImmersion b := by
    intro e
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) e
    change certifiedTorusImmersion u 1=certifiedTorusImmersion b 1 at h
    rw [ax _ hu,pb] at h
    linarith
  have ab : certifiedTorusImmersion a≠certifiedTorusImmersion b := by
    intro e
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) e
    change certifiedTorusImmersion a 1=certifiedTorusImmersion b 1 at h
    rw [pa,pb] at h
    linarith
  obtain ⟨B₀,_,_,_,_,away,safe,_⟩ := certified_embedding_axis_free_compact_test
  have ai : InjOn certifiedTorusImmersion axes :=
    safe.mono (fun x hx hB => disjoint_left.mp away hx hB)
  have injective : InjOn certifiedTorusImmersion A := by
    change InjOn _ (axes ∪ {a,b})
    rintro x (hx|rfl|hx) y (hy|rfl|hy) eq
    · exact ai hx hy eq
    · exact (disA _ hx eq).elim
    · rcases hy with rfl; exact (disB _ hx eq).elim
    · exact (disA _ hy eq.symm).elim
    · rfl
    · rcases hy with rfl; exact (ab eq).elim
    · rcases hx with rfl; exact (disB _ hy eq.symm).elim
    · rcases hx with rfl; exact (ab eq.symm).elim
    · exact hx.trans hy.symm
  let _ := certifiedTorusInducedMetricSpace
  obtain ⟨ac,ne⟩ := rhombicMarkedAxes_closed_and_nonempty p.height_pos
  have closed : IsClosed A := ac.union (Set.Finite.isClosed (Set.toFinite {a,b}))
  obtain ⟨dc,K,kc,sat,_⟩ := certified_compact_embedding_criterion
  obtain ⟨B,bc,sub,away,good,test⟩ := compact_collision_projection_off_injective_set
    certifiedTorusImmersion closed (ne.mono subset_union_left) injective kc dc sat
  refine ⟨injective,B,K,bc,kc,sub,away,good,⟨fun emb => test.mp emb.injective,fun h => ?_⟩⟩
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap certifiedTorusImmersion_continuous
    (test.mpr h) certifiedTorusImmersion_isProperMap.isClosedMap

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_embedding_away_from_axes_and_half_periods
