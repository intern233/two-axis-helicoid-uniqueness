import TwoAxisHelicoid.ActualTorusEndInjectivity
import TwoAxisHelicoid.CertifiedIntrinsicCompleteness
import TwoAxisHelicoid.SmoothImmersionLeftInverse

namespace TwoAxisHelicoid
open Complex Set Topology Filter
open scoped Topology ContDiff

/-- Ordered pairs of distinct parameter points with the same spatial position. -/
def immersionDoublePoints {M E : Type*} (X : M → E) : Set (M × M) :=
  {p | X p.1 = X p.2 ∧ p.1 ≠ p.2}

theorem isClosed_immersionDoublePoints {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    [T2Space E] {X : M → E} (hX : Continuous X)
    (hlocal : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ InjOn X U) :
    IsClosed (immersionDoublePoints X) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  rintro ⟨x,y⟩ hp
  by_cases same : X x = X y
  · have hxy : x = y := by
      by_contra h
      exact hp ⟨same,h⟩
    subst y
    obtain ⟨U,hU,hx,hI⟩ := hlocal x
    filter_upwards [(hU.prod hU).mem_nhds (show (x,x) ∈ U ×ˢ U from ⟨hx,hx⟩)] with p h
    exact fun he => he.2 (hI h.1 h.2 he.1)
  · have hC : IsClosed {p : M × M | X p.1 = X p.2} :=
      isClosed_eq (hX.comp continuous_fst) (hX.comp continuous_snd)
    filter_upwards [hC.isOpen_compl.mem_nhds (show (x,y) ∉ {p : M × M | X p.1 = X p.2} from same)] with p h
    exact fun he => h he.1

/-- A double point has both parameters in the saturated compact core.
Local injectivity also prevents double-point pairs accumulating on its diagonal. -/
theorem proper_immersion_compact_double_points {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    [T2Space E] {X : M → E} (hX : IsProperMap X)
    (hlocal : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ InjOn X U)
    {C : Set M} (hC : IsCompact C) (hend : InjOn X Cᶜ) :
    let K := X ⁻¹' (X '' C)
    IsCompact K ∧ immersionDoublePoints X ⊆ K ×ˢ K ∧ IsCompact (immersionDoublePoints X) ∧
      (IsClosedEmbedding X ↔ InjOn X K) := by
  let K := X ⁻¹' (X '' C)
  have hK : IsCompact K := hX.isCompact_preimage (hC.image hX.continuous)
  have hs : immersionDoublePoints X ⊆ K ×ˢ K := by
    rintro ⟨x,y⟩ ⟨he,hn⟩
    by_cases hx : x ∈ C
    · exact ⟨⟨x,hx,rfl⟩,⟨x,hx,he⟩⟩
    · by_cases hy : y ∈ C
      · exact ⟨⟨y,hy,he.symm⟩,⟨y,hy,rfl⟩⟩
      · exact (hn (hend hx hy he)).elim
  refine ⟨hK,hs,(hK.prod hK).of_isClosed_subset (isClosed_immersionDoublePoints hX.continuous hlocal) hs,
    fun h => h.injective.injOn,?_⟩
  intro h
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap hX.continuous _ hX.isClosedMap
  intro x y he
  by_contra hn
  have hb := hs (show (x,y) ∈ immersionDoublePoints X from ⟨he,hn⟩)
  exact hn (h hb.1 hb.2 he)

theorem certifiedTorusImmersion_locally_injective (q : PuncturedPeriodTorus certifiedPeriodPair) :
    ∃ U : Set (PuncturedPeriodTorus certifiedPeriodPair), IsOpen U ∧ q ∈ U ∧ InjOn certifiedTorusImmersion U := by
  let p := certifiedClosedParameters
  let L := certifiedPeriodPair
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  let Y := actualTorusImmersion p.height_pos p.abscissa_mem one_ne_zero p.vertical_closed p.horizontal_closed
  obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
  have hproj : periodTorusProjection L z = q.1 := hz
  have hreg : z ∉ L.lattice := fun h => q.2 (hproj.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
  have hm := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem
    (by norm_num : (1:ℝ) ≠ 0) p.vertical_closed p.horizontal_closed
  obtain ⟨g,V,hV,hzV,_,hg⟩ := smooth_local_left_inverse ((hm.2.1 z hreg).contDiffAt.of_le le_top)
    (hm.2.2.2 z hreg).2.1
  let U : Set (PuncturedPeriodTorus L) := Subtype.val ⁻¹' (periodTorusProjection L '' V)
  have hopen : IsOpenMap (periodTorusProjection L) := QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap
  refine ⟨U,(hopen V hV).preimage continuous_subtype_val,⟨z,hzV,hproj⟩,?_⟩
  rintro u ⟨x,hx,hxu⟩ v ⟨y,hy,hyv⟩ huv
  have h : coordinateToEuclidean (X x) = coordinateToEuclidean (X y) :=
    (congrArg (fun r => coordinateToEuclidean (Y r)) hxu).trans
      (huv.trans (congrArg (fun r => coordinateToEuclidean (Y r)) hyv).symm)
  have e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective h
  have hxy := (hg x hx).symm.trans ((congrArg g e).trans (hg y hy))
  exact Subtype.ext (hxu.symm.trans ((congrArg (periodTorusProjection L) hxy).trans hyv))

/-- The certified immersion is globally embedded exactly when it is injective on
one compact subset. This reduction uses the overtly constructed end and the
properness of the certified map, independently of embedded-existence theorems. -/
theorem certified_compact_embedding_criterion :
    IsCompact (immersionDoublePoints certifiedTorusImmersion) ∧
    ∃ K : Set (PuncturedPeriodTorus certifiedPeriodPair), IsCompact K ∧
      immersionDoublePoints certifiedTorusImmersion ⊆ K ×ˢ K ∧
      (IsClosedEmbedding certifiedTorusImmersion ↔ InjOn certifiedTorusImmersion K) := by
  let p := certifiedClosedParameters
  have h := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem
    (by norm_num : (1:ℝ) ≠ 0) p.vertical_closed p.horizontal_closed
  have hd : HasTwoAxisHelicoidCoordinateDifferential (actualGlobalImmersion p.t p.a 1 p.height_pos) p.t p.a 1 p.height_pos :=
    fun z hz => (h.2.2.2 z hz).1
  obtain ⟨C,hC,hI⟩ := actual_periodic_primitive_torus_end_injective p.height_pos p.abscissa_mem
    one_ne_zero hd h.1
  have hE : InjOn certifiedTorusImmersion Cᶜ := by
    intro x hx y hy e
    exact hI hx hy ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective e)
  obtain ⟨hK,hs,hD,hEq⟩ := proper_immersion_compact_double_points certifiedTorusImmersion_isProperMap
    certifiedTorusImmersion_locally_injective hC hE
  exact ⟨hD,_,hK,hs,hEq⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_compact_embedding_criterion
