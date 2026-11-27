import TwoAxisHelicoid.SlopingDoubleLoopSeparation
import TwoAxisHelicoid.RhombicSlopingCuts

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ComplexConjugate

private theorem injective_union_of_sides {M V : Type*} (F : M → V) (h : V → ℝ) (c : ℝ)
    {A B D : Set M} {o : M} (oa : o∈A) (a : InjOn F A) (b : InjOn F B) (d : InjOn F D)
    (zero : ∀ x∈A, h (F x)=c) (pos : ∀ x∈B, x=o ∨ c<h (F x)) (neg : ∀ x∈D, x=o ∨ h (F x)<c) :
    InjOn F (A ∪ B ∪ D) := by
  have ab {x y} (hx : x∈A) (hy : y∈B) (eq : F x=F y) : x=y := by
    rcases pos y hy with rfl|p
    · exact a hx oa eq
    · exact (p.ne ((congrArg h eq).symm.trans (zero x hx)).symm).elim
  have ad {x y} (hx : x∈A) (hy : y∈D) (eq : F x=F y) : x=y := by
    rcases neg y hy with rfl|p
    · exact a hx oa eq
    · exact (p.ne ((congrArg h eq).symm.trans (zero x hx))).elim
  have bd {x y} (hx : x∈B) (hy : y∈D) (eq : F x=F y) : x=y := by
    rcases pos x hx with rfl|p
    · exact ad oa hy eq
    rcases neg y hy with rfl|n
    · exact (ab oa hx eq.symm).symm
    · exact ((n.trans p).ne (congrArg h eq.symm)).elim
  rintro x ((hx|hx)|hx) y ((hy|hy)|hy) e
  · exact a hx hy e
  · exact ab hx hy e
  · exact ad hx hy e
  · exact (ab hy hx e.symm).symm
  · exact b hx hy e
  · exact bd hx hy e
  · exact (ad hy hx e.symm).symm
  · exact (bd hy hx e.symm).symm
  · exact d hx hy e

/-- The two entire marked axes and both sloping generator circles are
jointly injective in physical space. All possible remaining double
points have one endpoint in a compact set avoiding the four curves. -/
theorem certified_axis_and_cycle_injective_core_of_acceleration
    (acc : CheckedSlopingPositiveAcceleration (-3/16) (3/16)) :
    let p := certifiedClosedParameters
    let A := rhombicMarkedAxes p.t p.height_pos ∪ rhombicSlopingCycle p.height_pos false ∪ rhombicSlopingCycle p.height_pos true
    InjOn certifiedTorusImmersion A ∧ ∃ B K : Set (PuncturedPeriodTorus certifiedPeriodPair),
      IsCompact B ∧ IsCompact K ∧ B⊆K ∧ Disjoint A B ∧ InjOn certifiedTorusImmersion Bᶜ ∧
      (IsClosedEmbedding certifiedTorusImmersion ↔ ∀ x∈B, ∀ y∈K, certifiedTorusImmersion x=certifiedTorusImmersion y → x=y) := by
  intro p A
  let L := rhombicPeriodPair p.t p.height_pos
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  let T := actualTorusImmersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0) p.vertical_closed p.horizontal_closed
  let P := originalPeriodPath p.t
  let path := fun (b : Bool) (s : ℝ) => if b then conj (P s) else P s
  let π := periodTorusProjection L
  let axes := rhombicMarkedAxes p.t p.height_pos
  let cyc := rhombicSlopingCycle p.height_pos
  let J := Icc (-1:ℝ) 1
  let H := fun z => (X z 0,X z 1)
  have diff : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have per := actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  obtain ⟨tr,ar⟩ := certifiedClosedParameters_bounds
  have ht := Ioo_subset_Icc_self tr
  have ha := Ioo_subset_Icc_self ar
  obtain ⟨test,_⟩ := sloping_generator_horizontal_jordan ht ha p.height_pos diff per
  obtain ⟨_,side⟩ := sloping_cycles_transverse_sides ht ha p.height_pos diff per acc
  have off1 := real_not_mem_rhombic_lattice_of_pos p.height_pos (show (0:ℝ)<1 by norm_num) (show (1:ℝ)<2 by norm_num)
  let o : PuncturedPeriodTorus L := ⟨π 1,fun e => off1 ((periodTorusProjection_eq_zero L _).mp e)⟩
  have oa : o∈axes := Or.inl ⟨1,by norm_num [mem_Icc],rfl⟩
  have ep : P 1-P (-1)∈L.lattice := by
    convert L.lattice.sub_mem L.ω₁_mem_lattice L.ω₂_mem_lattice using 1
    change originalPeriodPath p.t 1-originalPeriodPath p.t (-1)=2-(1+I*p.t)
    simp only [originalPeriodPath,Complex.ofReal_neg,Complex.ofReal_one]
    ring
  have ends (b : Bool) : π (path b (-1))=π (path b 1) := by
    apply (periodTorusProjection_eq_iff L _ _).mpr
    cases b
    · exact ep
    · change conj (P 1)-conj (P (-1))∈L.lattice
      simpa only [map_sub] using rhombic_conj_mem p.height_pos ep
  have at0 (b : Bool) : π (path b 0)=o.1 := by
    have e : π (-1)=π 1 := (periodTorusProjection_eq_iff L _ _).mpr
      (by rw [show (1:ℂ)-(-1)=2 by norm_num]; exact L.ω₁_mem_lattice)
    cases b <;> simpa [path,P,originalPeriodPath,o] using e
  have value {u : PuncturedPeriodTorus L} {z : ℂ} (e : π z=u.1) : T u.1=X z := by rw [← e]; rfl
  have cy (b : Bool) : InjOn certifiedTorusImmersion (cyc b) := by
    intro x hx y hy eq
    obtain ⟨s,hs,ex⟩ := hx
    obtain ⟨v,hv,ey⟩ := hy
    have same : T x.1=T y.1 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective eq
    have coord : X (path b s)=X (path b v) := (value ex).symm.trans (same.trans (value ey))
    have hor : H (P s)=H (P v) := by
      cases b
      · exact Prod.ext (congrFun coord 0) (congrFun coord 1)
      · have x := congrFun coord 0
        have y := congrFun coord 1
        change X (conj (P s)) 0=X (conj (P v)) 0 at x
        change X (conj (P s)) 1=X (conj (P v)) 1 at y
        rw [(side s hs).1,(side v hv).1] at x
        rw [(side s hs).2.1,(side v hv).2.1] at y
        exact Prod.ext x (by change X (P s) 1=X (P v) 1; linarith)
    apply Subtype.ext
    apply ex.symm.trans
    apply Eq.trans _ ey
    rcases (test s hs v hv).mp hor with rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rfl
    · exact ends b
    · exact (ends b).symm
  let h := fun v : EuclideanSpace ℝ (Fin 3) => v 1
  have zero (x) (hx : x∈axes) : h (certifiedTorusImmersion x)=X 1 1 := by
    obtain ⟨z,hz,e⟩ := rhombicMarkedAxes_regular_representatives p.height_pos hx
    change T x.1 1=X 1 1
    rw [value e]
    rcases hz with ⟨r,hr,rfl⟩|⟨r,hr,rfl⟩
    · exact (actual_primitive_horizontal_line p.height_pos diff hr).1
    · exact (actual_primitive_vertical_line p.height_pos diff hr).2
  have pos (x) (hx : x∈cyc false) : x=o ∨ X 1 1<h (certifiedTorusImmersion x) := by
    obtain ⟨s,hs,e⟩ := hx
    by_cases z : s=0
    · subst s; exact Or.inl (Subtype.ext (e.symm.trans (at0 false)))
    · right
      change X 1 1<T x.1 1
      rw [value e]
      exact ((side s hs).2.2 z).1
  have neg (x) (hx : x∈cyc true) : x=o ∨ h (certifiedTorusImmersion x)<X 1 1 := by
    obtain ⟨s,hs,e⟩ := hx
    by_cases z : s=0
    · subst s; exact Or.inl (Subtype.ext (e.symm.trans (at0 true)))
    · right
      change T x.1 1<X 1 1
      rw [value e]
      exact ((side s hs).2.2 z).2
  obtain ⟨_,_,_,_,_,dis,good,_⟩ := certified_embedding_axis_free_compact_test
  have ai : InjOn certifiedTorusImmersion axes := good.mono (fun x hx hB => disjoint_left.mp dis hx hB)
  have inject : InjOn certifiedTorusImmersion A := injective_union_of_sides _ h _ oa ai (cy false) (cy true) zero pos neg
  let _ := certifiedTorusInducedMetricSpace
  obtain ⟨ac,ne⟩ := rhombicMarkedAxes_closed_and_nonempty p.height_pos
  have closed : IsClosed A := (ac.union (rhombicSlopingCycle_closed _ false)).union (rhombicSlopingCycle_closed _ true)
  obtain ⟨dc,K,kc,sat,_⟩ := certified_compact_embedding_criterion
  obtain ⟨B,bc,sub,away,safe,crit⟩ := compact_collision_projection_off_injective_set certifiedTorusImmersion
    closed ((ne.mono subset_union_left).mono subset_union_left) inject kc dc sat
  refine ⟨inject,B,K,bc,kc,sub,away,safe,⟨fun emb => crit.mp emb.injective,fun eq => ?_⟩⟩
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap certifiedTorusImmersion_continuous
    (crit.mpr eq) certifiedTorusImmersion_isProperMap.isClosedMap

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_axis_and_cycle_injective_core_of_acceleration
