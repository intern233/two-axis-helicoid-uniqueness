import TwoAxisHelicoid.SlopingGeneratorCircle
import TwoAxisHelicoid.SlopingAxisRateOrder

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ComplexConjugate

/-- The complete sloping cycle lies above the transverse axis except
at its marked crossing. Its conjugate lies below. The bounds apply to
the actual spatial primitive, uniformly on the root rectangle. -/
theorem sloping_cycles_transverse_sides {t a : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ha : a∈Icc (rootALower:ℝ) rootAUpper) (hp : 0<t) {X : ℂ → Fin 3 → ℝ}
    (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 hp)
    (per : ∀ z p, p∈(rhombicPeriodPair t hp).lattice → X (z+p)=X z)
    (acc : CheckedSlopingPositiveAcceleration (-3/16) (3/16)) :
    let P := originalPeriodPath t
    X (P 0)=X 1 ∧ ∀ s∈Icc (-1:ℝ) 1,
      X (conj (P s)) 0=X (P s) 0 ∧ X (conj (P s)) 1=2*X 1 1-X (P s) 1 ∧
      (s≠0 → X 1 1<X (P s) 1 ∧ X (conj (P s)) 1<X 1 1) := by
  intro P
  have zero : X (P 0)=X 1 := by
    have e := per (-1) 2 (rhombicPeriodPair t hp).ω₁_mem_lattice
    rw [show (-1:ℂ)+2=1 by norm_num] at e
    simpa [P,originalPeriodPath] using e.symm
  refine ⟨zero,?_⟩
  intro s hs
  have off := rhombic_open_rectangle_not_mem hp (originalPeriodPath_mem_rectangle hp hs)
  have ref := (explicit_centered_primitive_reflections hp d per _ off).2
  have re := congrFun ref 0
  have im := congrFun ref 1
  change X (conj (P s)) 0-X 1 0=X (P s) 0-X 1 0 at re
  change X (conj (P s)) 1-X 1 1= -(X (P s) 1-X 1 1) at im
  refine ⟨by linarith,by linarith,fun ne => ?_⟩
  have above {v : ℝ} (hv : v∈Ioc (0:ℝ) 1) : X 1 1<X (P v) 1 := by
    have h := sloping_transverse_positive_on_half ht ha hp d acc v hv
    change X (P 0) 1<X (P v) 1 at h
    rwa [zero] at h
  have pos : X 1 1<X (P s) 1 := by
    rcases lt_or_gt_of_ne ne with neg|pos
    · have val := congrArg Prod.snd (sloping_generator_reflected_horizontal hp d per hs)
      exact (above (v:= -s) ⟨neg_pos.mpr neg,by linarith [hs.1]⟩).trans_eq val
    · exact above ⟨pos,hs.2⟩
  exact ⟨pos,by linarith⟩

/-- The horizontal projections of the two fundamental sloping cycles
are embedded circles. Their images meet at exactly the axes crossing. -/
theorem sloping_cycles_horizontal_bouquet {t a : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ha : a∈Icc (rootALower:ℝ) rootAUpper) (hp : 0<t) {X : ℂ → Fin 3 → ℝ}
    (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 hp)
    (per : ∀ z p, p∈(rhombicPeriodPair t hp).lattice → X (z+p)=X z)
    (acc : CheckedSlopingPositiveAcceleration (-3/16) (3/16)) :
    let P := originalPeriodPath t
    let H := fun z => (X z 0,X z 1)
    ∃ G J : AddCircle (2:ℝ) → ℝ × ℝ, IsClosedEmbedding G ∧ IsClosedEmbedding J ∧
      (∀ s∈Icc (-1:ℝ) 1, G (s:AddCircle (2:ℝ))=H (P s) ∧ J (s:AddCircle (2:ℝ))=H (conj (P s))) ∧
      range G ∩ range J={H 1} := by
  intro P H
  obtain ⟨_,G,emb,point⟩ := sloping_generator_horizontal_jordan ht ha hp d per
  obtain ⟨zero,side⟩ := sloping_cycles_transverse_sides ht ha hp d per acc
  let T : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
    toFun := fun v => (v.1,2*X 1 1-v.2)
    invFun := fun v => (v.1,2*X 1 1-v.2)
    left_inv := fun v => Prod.ext rfl (by dsimp; ring)
    right_inv := fun v => Prod.ext rfl (by dsimp; ring)
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let J := T ∘ G
  have agree (s : ℝ) (hs : s∈Icc (-1:ℝ) 1) : J (s:AddCircle (2:ℝ))=H (conj (P s)) := by
    change T (G (s:AddCircle (2:ℝ)))=_
    rw [point s hs]
    exact Prod.ext (side s hs).1.symm (side s hs).2.1.symm
  let _ : Fact (0<(2:ℝ)) := ⟨by norm_num⟩
  have rep (u : AddCircle (2:ℝ)) : ∃ s∈Icc (-1:ℝ) 1, (s:AddCircle (2:ℝ))=u := by
    let e := AddCircle.equivIco (2:ℝ) (-1)
    refine ⟨(e u).1,⟨(e u).2.1,?_⟩,AddCircle.coe_equivIco (a:=(-1:ℝ))⟩
    have h := (e u).2.2
    change (e u).1<(-1:ℝ)+2 at h
    linarith
  have cent : H (P 0)=H 1 := Prod.ext (congrFun zero 0) (congrFun zero 1)
  have cconj : H (conj (P 0))=H 1 := by
    have eq : conj (P 0)=P 0 := by simp [P,originalPeriodPath]
    rw [eq,cent]
  have z : (0:ℝ)∈Icc (-1:ℝ) 1 := by norm_num [mem_Icc]
  refine ⟨G,J,emb,T.isClosedEmbedding.comp emb,fun s hs => ⟨point s hs,agree s hs⟩,?_⟩
  ext v
  constructor
  · rintro ⟨⟨u,hu⟩,⟨w,hw⟩⟩
    obtain ⟨s,hs,rfl⟩ := rep u
    obtain ⟨r,hr,rfl⟩ := rep w
    have eq : H (P s)=H (conj (P r)) := (point s hs).symm.trans (hu.trans (hw.symm.trans (agree r hr)))
    by_cases zeroS : s=0
    · subst s
      exact hu.symm.trans ((point 0 z).trans cent)
    · have high := ((side s hs).2.2 zeroS).1
      have same := congrArg Prod.snd eq
      change X (P s) 1=X (conj (P r)) 1 at same
      by_cases zeroR : r=0
      · subst r
        have eq0 := congrArg Prod.snd cconj
        change X (conj (P 0)) 1=X 1 1 at eq0
        linarith
      · have low := ((side r hr).2.2 zeroR).2
        linarith
  · rintro rfl
    exact ⟨⟨(0:ℝ),(point 0 z).trans cent⟩,⟨(0:ℝ),(agree 0 z).trans cconj⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.sloping_cycles_horizontal_bouquet
