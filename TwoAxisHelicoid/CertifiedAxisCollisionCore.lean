import TwoAxisHelicoid.CompactDoublePointsAwayFromAxes
import TwoAxisHelicoid.ExplicitEmbeddedAxes

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology

/-- The closed pair of marked straight axes on the punctured rhombic
torus. The endpoints of the compact intervals represent its puncture. -/
def rhombicMarkedAxes (t : ℝ) (ht : 0<t) : Set (PuncturedPeriodTorus (rhombicPeriodPair t ht)) :=
  let π := periodTorusProjection (rhombicPeriodPair t ht)
  Subtype.val ⁻¹' (((fun r : ℝ => π (r:ℂ)) '' Icc 0 2) ∪ ((fun r : ℝ => π (1+I*r)) '' Icc (-t) t))

theorem rhombicMarkedAxes_closed_and_nonempty {t : ℝ} (ht : 0<t) :
    IsClosed (rhombicMarkedAxes t ht) ∧ (rhombicMarkedAxes t ht).Nonempty := by
  let L := rhombicPeriodPair t ht
  let _ : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  have ct : Continuous (periodTorusProjection L) := QuotientAddGroup.continuous_mk
  refine ⟨?_,?_⟩
  · apply IsClosed.preimage continuous_subtype_val
    exact ((isCompact_Icc.image (ct.comp continuous_ofReal)).union
      (isCompact_Icc.image (ct.comp (continuous_const.add (continuous_const.mul continuous_ofReal))))).isClosed
  · have off := real_not_mem_rhombic_lattice_of_pos ht (show (0:ℝ)<1 by norm_num) (show (1:ℝ)<2 by norm_num)
    let q : PuncturedPeriodTorus L := ⟨periodTorusProjection L (1:ℝ),fun e => off ((periodTorusProjection_eq_zero L _).mp e)⟩
    exact ⟨q,Or.inl ⟨1,⟨by norm_num,by norm_num⟩,rfl⟩⟩

private theorem regular_axis_interval {L : PeriodPair} (f : ℝ → ℂ) {l h : ℝ} (left : f l∈L.lattice)
    (right : f h∈L.lattice) {q : PuncturedPeriodTorus L} {r : ℝ} (closed : r∈Icc l h)
    (pos : periodTorusProjection L (f r)=q.1) : r∈Ioo l h := by
  have off : f r∉L.lattice := fun mem => q.2 (pos.symm.trans ((periodTorusProjection_eq_zero L _).mpr mem))
  exact ⟨lt_of_le_of_ne closed.1 (fun e => off (e ▸ left)),
    lt_of_le_of_ne closed.2 (fun e => off (e.symm ▸ right))⟩

theorem rhombicMarkedAxes_regular_representatives {t : ℝ} (ht : 0<t) {q : PuncturedPeriodTorus (rhombicPeriodPair t ht)}
    (hq : q∈rhombicMarkedAxes t ht) : ∃ z∈(Complex.ofReal '' Ioo (0:ℝ) 2) ∪ ((fun r : ℝ => 1+I*r) '' Ioo (-t) t),
      periodTorusProjection (rhombicPeriodPair t ht) z=q.1 := by
  let L := rhombicPeriodPair t ht
  rcases hq with ⟨r,hr,pr⟩|⟨r,hr,pr⟩
  · have end₀ : ((0:ℝ):ℂ)∈L.lattice := by simp
    have end₂ : ((2:ℝ):ℂ)∈L.lattice := by rw [Complex.ofReal_ofNat]; exact L.ω₁_mem_lattice
    exact ⟨_,Or.inl ⟨r,regular_axis_interval Complex.ofReal end₀ end₂ hr pr,rfl⟩,pr⟩
  · have low : 1+I*(-t:ℝ)∈L.lattice := by
      apply PeriodPair.mem_lattice.mpr
      refine ⟨1,-1,?_⟩
      simp only [L,rhombicPeriodPair,Int.cast_one,Int.cast_neg,Complex.ofReal_neg]
      ring
    have high : 1+I*(t:ℝ)∈L.lattice := L.ω₂_mem_lattice
    exact ⟨_,Or.inr ⟨r,regular_axis_interval (fun s : ℝ => 1+I*s) low high hr pr,rfl⟩,pr⟩

/-- The whole certified immersion is already injective on an open set
containing both entire axes and the end. Every collision involves the
compact axis-free set B and another point of the saturated compact K. -/
theorem certified_embedding_axis_free_compact_test :
    let A := rhombicMarkedAxes certifiedClosedParameters.t certifiedClosedParameters.height_pos
    ∃ B K : Set (PuncturedPeriodTorus certifiedPeriodPair),
      IsCompact B ∧ IsCompact K ∧ B⊆K ∧ Disjoint A B ∧ InjOn certifiedTorusImmersion Bᶜ ∧
      (IsClosedEmbedding certifiedTorusImmersion ↔ ∀ x∈B, ∀ y∈K, certifiedTorusImmersion x=certifiedTorusImmersion y → x=y) := by
  let p := certifiedClosedParameters
  let A := rhombicMarkedAxes p.t p.height_pos
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  let Y := actualTorusImmersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed
  have h := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed
  have diff : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz => (h.2.2.2 z hz).1
  have inj : InjOn certifiedTorusImmersion A := by
    intro x hx y hy eq
    obtain ⟨u,hu,ex⟩ := rhombicMarkedAxes_regular_representatives p.height_pos hx
    obtain ⟨v,hv,ey⟩ := rhombicMarkedAxes_regular_representatives p.height_pos hy
    have xy : Y x.1=Y y.1 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective eq
    rw [← ex,← ey] at xy
    have uv := actual_primitive_injective_on_both_axes p.height_pos p.abscissa_mem one_ne_zero diff hu hv xy
    exact Subtype.ext (ex.symm.trans ((congrArg (periodTorusProjection certifiedPeriodPair) uv).trans ey))
  obtain ⟨dc,K,kc,sat,_⟩ := certified_compact_embedding_criterion
  obtain ⟨ac,ne⟩ := rhombicMarkedAxes_closed_and_nonempty p.height_pos
  obtain ⟨B,bc,sub,away,good,test⟩ := @compact_collision_projection_off_injective_set _ _ certifiedTorusInducedMetricSpace
    certifiedTorusImmersion A K ac ne inj kc dc sat
  refine ⟨B,K,bc,kc,sub,away,good,⟨fun emb => test.mp emb.injective,fun t => ?_⟩⟩
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap certifiedTorusImmersion_continuous
    (test.mpr t) certifiedTorusImmersion_isProperMap.isClosedMap

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombicMarkedAxes_closed_and_nonempty
#print axioms TwoAxisHelicoid.certified_embedding_axis_free_compact_test
