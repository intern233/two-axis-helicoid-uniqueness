import TwoAxisHelicoid.EquivariantPuncturedTorusFlow
import TwoAxisHelicoid.HighHorizontalHeightFibers
import TwoAxisHelicoid.RegularHeightTranslation

namespace TwoAxisHelicoid
open Complex Set Topology

private theorem far_height_same_side (x b A : ℝ) {h : ℝ} (hne : h≠0) :
    ∃ u : ℝ, ((0<u ∧ 0<h) ∨ (u<0 ∧ h<0)) ∧ A < |x+u-b| := by
  let v := |A|+|x-b|+1
  have pos : 0<v := by dsimp [v]; positivity
  rcases lt_or_gt_of_ne hne with hn|hp
  · refine ⟨-v,Or.inr ⟨neg_lt_zero.mpr pos,hn⟩,?_⟩
    apply lt_of_lt_of_le _ (neg_le_abs _)
    dsimp [v]
    linarith [le_abs_self A,le_abs_self (x-b)]
  · refine ⟨v,Or.inl ⟨pos,hp⟩,?_⟩
    apply lt_of_lt_of_le _ (le_abs_self _)
    dsimp [v]
    linarith [le_abs_self A,neg_le_abs (x-b)]

/-- Every regular noncentral horizontal fiber of the actual punctured
torus is one properly embedded real line in its parameter surface.
There is a continuous plane lift on which the imaginary part of the
unmodified complex height is exactly the real parameter. -/
theorem actual_regular_horizontal_fibers {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (period : ∀ z w, w∈(rhombicPeriodPair t ht).lattice → X (z+w)=X z) {h : ℝ} (hne : h≠0) :
    let L := rhombicPeriodPair t ht
    let H := actualComplexHeight t a c ht
    let Y := fun q : PuncturedPeriodTorus L => periodTorusLift L X period q.1
    ∃ (g : ℝ → ℂ) (s : ℝ) (q : ℝ → PuncturedPeriodTorus L),
      Continuous g ∧ (∀ y, g y∉L.lattice ∧ H (g y)=⟨s,y⟩ ∧ (q y).1=periodTorusProjection L (g y)) ∧
      IsClosedEmbedding q ∧ range q={p | Y p 2=X 1 2+h} := by
  let L := rhombicPeriodPair t ht
  let H := actualComplexHeight t a c ht
  let Y := fun q : PuncturedPeriodTorus L => periodTorusLift L X period q.1
  obtain ⟨K,b,A,high⟩ := actual_high_horizontal_height_fibers ht ha hc diff period
  obtain ⟨u,side,far⟩ := far_height_same_side (X 1 2) b A hne
  let v := X 1 2+u-b
  obtain ⟨source,embed,all,cK⟩ := high v far
  let d : ℂ := ((h-u:ℝ):ℂ)
  obtain ⟨F,per,fixed,forward,back⟩ := actual_regular_height_translation ht ha hc diff period side (b := d) rfl
  obtain ⟨E,proj,_⟩ := equivariant_punctured_torus_homeomorph L F per (fixed 0 L.lattice.zero_mem)
  let k := fun y : ℝ => K ⟨v,y⟩
  let p := fun y : ℝ => (⟨periodTorusProjection L (k y),fun eq => (source y).1 ((periodTorusProjection_eq_zero L _).mp eq)⟩ : PuncturedPeriodTorus L)
  let g := F ∘ k
  let q := E ∘ p
  have pr (y : ℝ) : (q y).1=periodTorusProjection L (g y) := proj (p y) (k y) rfl
  have level (y : ℝ) : X (k y) 2=X 1 2+u := (source y).2.2.trans (sub_add_cancel _ _)
  have properties (y : ℝ) := forward _ (source y).1 (level y)
  have cY : Continuous Y := periodTorusLift_continuous_punctured L X period (fun z hz => (diff z hz).continuousAt)
  have cp : Continuous p := Continuous.subtype_mk (QuotientAddGroup.continuous_mk.comp cK) _
  have ep : IsEmbedding p := IsEmbedding.of_comp cp cY embed.isEmbedding
  have eqEmb : IsEmbedding q := E.isEmbedding.comp ep
  have rangeEq : range q={x | Y x 2=X 1 2+h} := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      have eq : Y (q y)=X (g y) := congrArg (periodTorusLift L X period) (pr y)
      exact (congrFun eq 2).trans (properties y).2.2
    · intro hx
      obtain ⟨z,hz⟩ := Quotient.exists_rep x.1
      change periodTorusProjection L z=x.1 at hz
      have off : z∉L.lattice := fun h => x.2 (hz.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
      have eq : X z=Y x := congrArg (periodTorusLift L X period) hz
      obtain ⟨nl,_,lev⟩ := back _ off ((congrFun eq 2).trans hx)
      obtain ⟨y,py,_⟩ := all (F.symm z) nl (by rw [lev]; exact (sub_add_cancel _ _).symm)
      let p' : PuncturedPeriodTorus L := ⟨periodTorusProjection L (F.symm z),fun eq => nl ((periodTorusProjection_eq_zero L _).mp eq)⟩
      have pe : p y=p' := Subtype.ext py
      refine ⟨y,Subtype.ext ?_⟩
      change (E (p y)).1=x.1
      rw [pe,proj p' (F.symm z) rfl,F.apply_symm_apply,hz]
  refine ⟨g,X 1 2+h-b,q,F.continuous.comp cK,?_,⟨eqEmb,?_⟩,rangeEq⟩
  · intro y
    refine ⟨(properties y).1,?_,pr y⟩
    change H (F (k y))=_
    rw [show H (F (k y))=H (k y)+d from (properties y).2.1,show H (k y)=⟨v,y⟩ from (source y).2.1]
    apply Complex.ext
    · change v+(h-u)=X 1 2+h-b
      dsimp [v]
      ring
    · change y+0=y
      ring
  · rw [rangeEq]
    exact isClosed_eq ((continuous_apply 2).comp cY) continuous_const

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_regular_horizontal_fibers
