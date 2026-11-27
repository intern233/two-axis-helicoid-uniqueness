import TwoAxisHelicoid.MarkedTorusCircleCoordinates
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Order.Compact

namespace TwoAxisHelicoid
open Set Topology Filter Function
open scoped Topology OnePoint

/-- Finite embedded compact loops meeting at one base point carry a
common phase lift as soon as each loop does. The additive constants
are fixed at the base point before descending along the quotient. -/
theorem phase_lift_on_finite_bouquet {ι T X : Type*} [Finite ι] [TopologicalSpace T] [CompactSpace T]
    [TopologicalSpace X] [T2Space X] (g : ι → C(T,X)) (p : X) (b : T)
    (based : ∀ i, g i b=p) (inj : ∀ i, Injective (g i))
    (apart : ∀ i j, i≠j → ∀ t u, g i t=g j u → g i t=p)
    (cover : ∀ x, ∃ i t, g i t=x) (φ : C(X,Circle))
    (localLift : ∀ i, ∃ u : C(T,ℝ), ∀ t, normalizedPhase (u t)=φ (g i t)) :
    ∃ U : C(X,ℝ), ∀ x, normalizedPhase (U x)=φ x := by
  classical
  choose u rep using localLift
  let k := ((φ p : Circle) : ℂ).arg/(2*Real.pi)
  have angle : normalizedPhase k=φ p := by
    change Circle.exp (2*Real.pi*(((φ p : Circle) : ℂ).arg/(2*Real.pi)))=φ p
    rw [show 2*Real.pi*(((φ p : Circle) : ℂ).arg/(2*Real.pi))=((φ p : Circle) : ℂ).arg by field_simp,
      Circle.exp_arg]
  let S := Σ _ : ι, T
  let π := fun y : S => g y.1 y.2
  have cπ : Continuous π := continuous_sigma_iff.mpr (fun i => (g i).continuous)
  have sur : Surjective π := by
    intro x
    obtain ⟨i,t,hit⟩ := cover x
    exact ⟨⟨i,t⟩,hit⟩
  have qt : IsQuotientMap π := cπ.isClosedMap.isQuotientMap cπ sur
  let f := fun y : S => u y.1 y.2-u y.1 b+k
  have cf : Continuous f := by
    apply continuous_sigma_iff.mpr
    intro i
    change Continuous (fun t => u i t-u i b+k)
    exact ((u i).continuous.sub (continuous_const (y:=u i b))).add (continuous_const (y:=k))
  have fibers : ∀ x y, π x=π y → f x=f y := by
    rintro ⟨i,t⟩ ⟨j,s⟩ same
    change g i t=g j s at same
    by_cases eq : i=j
    · subst j
      rw [(inj i) same]
    · have hit := apart i j eq t s same
      have t0 : t=b := inj i (hit.trans (based i).symm)
      have s0 : s=b := inj j (same.symm.trans (hit.trans (based j).symm))
      simp [f,t0,s0]
  refine ⟨⟨_,quotientFiberDescend_continuous qt f fibers cf⟩,?_⟩
  rintro x
  obtain ⟨⟨i,t⟩,rfl⟩ := sur x
  change normalizedPhase (quotientFiberDescend π _ f (π ⟨i,t⟩))=φ (g i t)
  rw [quotientFiberDescend_apply _ _ _ fibers]
  change Circle.exp (2*Real.pi*((u i t-u i b)+k))=φ (g i t)
  rw [mul_add,mul_sub,Circle.exp_add,Circle.exp_sub]
  change normalizedPhase (u i t)/normalizedPhase (u i b)*normalizedPhase k=φ (g i t)
  rw [rep i t,rep i b,based,angle,div_mul_cancel]

/-- An obstruction in either marked circle on the compact bouquet
occurs on one of its actual embedded loops. -/
theorem nonlifting_pair_on_one_bouquet_loop {ι T X : Type*} [Finite ι] [TopologicalSpace T] [CompactSpace T]
    [TopologicalSpace X] [T2Space X] (g : ι → C(T,X)) (p : X) (b : T)
    (based : ∀ i, g i b=p) (inj : ∀ i, Injective (g i))
    (apart : ∀ i j, i≠j → ∀ t u, g i t=g j u → g i t=p)
    (cover : ∀ x, ∃ i t, g i t=x) (H : C(X,Circle×Circle))
    (nonlift : ¬∃ u w : C(X,ℝ), ∀ x, normalizedPhase (u x)=(H x).1 ∧ normalizedPhase (w x)=(H x).2) :
    ∃ i, ¬∃ u w : C(T,ℝ), ∀ t, normalizedPhase (u t)=(H (g i t)).1 ∧
      normalizedPhase (w t)=(H (g i t)).2 := by
  classical
  by_contra! allLift
  choose u w rep using allLift
  obtain ⟨U,hu⟩ := phase_lift_on_finite_bouquet g p b based inj apart cover
    ⟨_,H.continuous.fst⟩ (fun i => ⟨u i,fun t => (rep i t).1⟩)
  obtain ⟨W,hw⟩ := phase_lift_on_finite_bouquet g p b based inj apart cover
    ⟨_,H.continuous.snd⟩ (fun i => ⟨w i,fun t => (rep i t).2⟩)
  exact nonlift ⟨U,W,fun x => ⟨hu x,hw x⟩⟩

/-- The two infinite ends of an injective regular orbit give a single
point in its compactification, including the value of the actual map
at that point. -/
theorem compactified_two_ended_orbit {X : Type*} [TopologicalSpace X] (p : X) (γ : C(ℝ,X))
    (avoid : ∀ t, γ t≠p) (inj : Injective γ)
    (positive : Tendsto γ atTop (𝓝 p)) (negative : Tendsto γ atBot (𝓝 p)) :
    ∃ g : C(OnePoint ℝ,X), g ∞=p ∧ (∀ t : ℝ, g t=γ t) ∧ Injective g := by
  have limit : Tendsto γ (coclosedCompact ℝ) (𝓝 p) := by
    rw [coclosedCompact_eq_cocompact,cocompact_eq_atBot_atTop]
    exact negative.sup positive
  let g := OnePoint.continuousMapMk γ p limit
  refine ⟨g,rfl,fun _ => rfl,?_⟩
  intro x y
  induction x using OnePoint.rec <;> induction y using OnePoint.rec
  · exact fun _ => rfl
  · rename_i y
    exact fun eq => ((avoid y) eq.symm).elim
  · rename_i x
    exact fun eq => ((avoid x) eq).elim
  · exact fun eq => congrArg OnePoint.some (inj eq)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.nonlifting_pair_on_one_bouquet_loop
#print axioms TwoAxisHelicoid.compactified_two_ended_orbit
