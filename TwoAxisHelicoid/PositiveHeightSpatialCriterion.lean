import TwoAxisHelicoid.HorizontalFiberChordIntegral
import TwoAxisHelicoid.ExplicitMarkedReflections

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Topology
open scoped Interval

/-- The negative physical levels are determined by the half turn about
the transverse axis. For full spatial injectivity one may therefore use
only the central slice and the actual weighted Gauss integrals on
positive levels. -/
theorem actual_positive_height_embedding_test {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z) :
    let L := rhombicPeriodPair t ht
    let Y := fun p : PuncturedPeriodTorus L => periodTorusLift L X per p.1
    ∃ (g : Ioi (0:ℝ) → ℝ → ℂ) (q : Ioi (0:ℝ) → ℝ → PuncturedPeriodTorus L),
      (∀ h, Continuous (g h) ∧ IsClosedEmbedding (q h) ∧ range (q h)={p | Y p 2=X 1 2+h.1} ∧
        (∀ y, (q h y).1=periodTorusProjection L (g h y)) ∧
        (InjOn Y (range (q h)) ↔ ∀ u v, u<v → (∫ y in u..v,horizontalWeightedGauss t a (g h) y)≠0)) ∧
      (Function.Injective Y ↔ InjOn Y {p | Y p 2=X 1 2} ∧
        ∀ h u v, u<v → (∫ y in u..v,horizontalWeightedGauss t a (g h) y)≠0) := by
  classical
  intro L Y
  have levels (h : Ioi (0:ℝ)) := actual_noncentral_level_embedding_test ht ha one_ne_zero d per h.2.ne'
  choose g q cg eqb image agree iff using levels
  refine ⟨g,q,fun h => ⟨cg h,eqb h,image h,agree h,iff h⟩,?_⟩
  constructor
  · intro hi
    exact ⟨hi.injOn,fun h => (iff h).mp hi.injOn⟩
  · rintro ⟨center,tests⟩
    let N := fun p : PuncturedPeriodTorus L => (⟨-p.1,neg_ne_zero.mpr p.2⟩ : PuncturedPeriodTorus L)
    have reflect (p : PuncturedPeriodTorus L) :
        Y (N p)-X 1= ![-(Y p-X 1) 0,(Y p-X 1) 1,-(Y p-X 1) 2] := by
      obtain ⟨z,e⟩ := Quotient.exists_rep p.1
      change periodTorusProjection L z=p.1 at e
      have off := fun h => p.2 (e.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
      have ne : periodTorusProjection L (-z)= -(periodTorusProjection L z) := rfl
      change periodTorusLift L X per (-p.1)-X 1=_
      dsimp only [Y]
      rw [← e,← ne]
      exact (explicit_centered_primitive_reflections ht d per z off).1
    have above {p v : PuncturedPeriodTorus L} (hp : X 1 2<Y p 2) (same : Y p=Y v) : p=v := by
      let h : Ioi (0:ℝ) := ⟨Y p 2-X 1 2,sub_pos.mpr hp⟩
      have lev : p∈range (q h) := by
        rw [image]
        change Y p 2=X 1 2+(Y p 2-X 1 2)
        ring
      have lev' : v∈range (q h) := by
        rw [image] at lev ⊢
        change Y v 2=X 1 2+h.1
        rwa [← same]
      exact ((iff h).mpr (tests h)) lev lev' same
    intro p v same
    rcases lt_trichotomy (Y p 2) (X 1 2) with low|mid|high
    · have h : Y (N p)=Y (N v) := sub_left_inj.mp
        ((reflect p).trans (by rw [same]; exact (reflect v).symm))
      have e := congrFun (reflect p) 2
      change Y (N p) 2-X 1 2= -(Y p 2-X 1 2) at e
      have eq := congrArg Subtype.val (above (by linarith) h)
      exact Subtype.ext (neg_injective eq)
    · exact center mid (by change Y v 2=_; rwa [← same]) same
    · exact above high same

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_positive_height_embedding_test
