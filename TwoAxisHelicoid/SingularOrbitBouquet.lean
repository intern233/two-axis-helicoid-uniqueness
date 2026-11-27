import TwoAxisHelicoid.FiniteBouquetPhaseLifts
import TwoAxisHelicoid.RegularOrbitEndsAtSaddle

namespace TwoAxisHelicoid
open Set Filter Topology Function
open scoped Topology OnePoint

/-- Intersecting orbits of a time action have exactly the same range. -/
theorem time_orbit_range_of_meeting {Y : Type*} (Φ : ℝ → Y → Y)
    (add : ∀ a b x, Φ (a+b) x=Φ a (Φ b x)) {x y : Y} {r s : ℝ} (meet : Φ r x=Φ s y) :
    range (fun t => Φ t x)=range (fun t => Φ t y) := by
  have shift (p : Y) (t : ℝ) : range (fun u => Φ u (Φ t p))=range (fun u => Φ u p) := by
    ext q
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨u+t,add u t p⟩
    · rintro ⟨u,rfl⟩
      exact ⟨u-t,by change Φ (u-t) (Φ t p)=Φ u p; rw [← add,sub_add_cancel]⟩
  rw [← shift x r,meet,shift]

/-- For a singular component covered by finitely many regular orbits
and one point, absence of a common marked lift is detected by a single
actual orbit with both ends compactified at the singular point. -/
theorem singular_component_obstructed_orbit {Y ι : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [Finite ι] [Nonempty ι] (p : Y) (Φ : ℝ → ({p}ᶜ : Set Y) → ({p}ᶜ : Set Y))
    (start : ∀ x, Φ 0 x=x) (add : ∀ a b x, Φ (a+b) x=Φ a (Φ b x))
    (cont : ∀ x, Continuous (fun t => Φ t x)) (op : ∀ x, IsOpenMap (fun t => Φ t x))
    (seeds : ι → ({p}ᶜ : Set Y)) (belong : ∀ i, (seeds i).1∈connectedComponent p)
    (cover : ∀ x : ({p}ᶜ : Set Y), x.1∈connectedComponent p → ∃ i t, Φ t (seeds i)=x)
    (H : C(Y,Circle×Circle))
    (obstruct : ¬∃ u w : C(connectedComponent p,ℝ), ∀ q : connectedComponent p,
      normalizedPhase (u q)=(H q.1).1 ∧ normalizedPhase (w q)=(H q.1).2) :
    ∃ (x : ({p}ᶜ : Set Y)) (g : C(OnePoint ℝ,Y)), x.1∈connectedComponent p ∧ g ∞=p ∧
      (∀ t : ℝ, g t=(Φ t x).1) ∧ Injective g ∧
      ¬∃ u w : C(OnePoint ℝ,ℝ), ∀ t, normalizedPhase (u t)=(H (g t)).1 ∧ normalizedPhase (w t)=(H (g t)).2 := by
  classical
  let C := connectedComponent p
  let D := ({p}ᶜ : Set Y)
  let base : C := ⟨p,mem_connectedComponent⟩
  let S := fun i => range (fun t => Φ t (seeds i))
  let J := range S
  let : Finite J := (finite_range S).to_subtype
  choose idx hidx using (fun j : J => j.2)
  let x := fun j : J => seeds (idx j)
  have within (j : J) (t : ℝ) : (Φ t (x j)).1∈C := by
    have path := isPreconnected_range (continuous_subtype_val.comp (cont (x j)))
    have first : (x j).1∈range (fun t => (Φ t (x j)).1) := ⟨0,congrArg Subtype.val (start _)⟩
    rw [show C=connectedComponent (x j).1 from connectedComponent_eq (belong _)]
    exact path.subset_connectedComponent first (mem_range_self t)
  let f := fun j (t : ℝ) => (⟨(Φ t (x j)).1,within j t⟩ : C)
  have each (j : J) : ∃ g : C(OnePoint ℝ,C), g ∞=base ∧ (∀ t : ℝ, g t=f j t) ∧ Injective g := by
    obtain ⟨emb,top,bot⟩ := regular_orbit_in_singular_component p Φ start add cont op (x j) (belong _)
    have cv : Continuous (f j) := (continuous_subtype_val.comp (cont _)).subtype_mk _
    apply compactified_two_ended_orbit base ⟨f j,cv⟩
    · exact fun t eq => (Φ t (x j)).2 (congrArg Subtype.val eq)
    · intro u v eq
      exact emb.injective (Subtype.ext (congrArg (fun q : C => q.1) eq))
    · exact tendsto_subtype_rng.mpr top
    · exact tendsto_subtype_rng.mpr bot
  choose g based real gi using each
  have apart (i j : J) (diff : i≠j) (s t : OnePoint ℝ) (same : g i s=g j t) : g i s=base := by
    induction s using OnePoint.rec with
    | infty => exact based i
    | coe u =>
      induction t using OnePoint.rec with
      | infty => exact same.trans (based j)
      | coe v =>
        rw [real,real] at same
        have meet : Φ u (x i)=Φ v (x j) := Subtype.ext (congrArg (fun q : C => q.1) same)
        have ranges := time_orbit_range_of_meeting Φ add meet
        exact False.elim (diff (Subtype.ext ((hidx i).symm.trans (ranges.trans (hidx j)))))
  have full (q : C) : ∃ j t, g j t=q := by
    by_cases eq : q.1=p
    · let i : ι := Classical.choice inferInstance
      let j : J := ⟨S i,mem_range_self i⟩
      exact ⟨j,∞,(based j).trans (Subtype.ext eq.symm)⟩
    let y : D := ⟨q.1,eq⟩
    obtain ⟨i,t,hit⟩ := cover y q.2
    let j : J := ⟨S i,mem_range_self i⟩
    have member : y∈S (idx j) := (hidx j).symm ▸ (show y∈S i from ⟨t,hit⟩)
    obtain ⟨u,hu⟩ := member
    exact ⟨j,(u:OnePoint ℝ),(real j u).trans (Subtype.ext (congrArg (fun q : D => q.1) hu))⟩
  let incl : C(C,Y) := ⟨Subtype.val,continuous_subtype_val⟩
  obtain ⟨j,fail⟩ := nonlifting_pair_on_one_bouquet_loop g base ∞ based gi apart full (H.comp incl) obstruct
  refine ⟨x j,incl.comp (g j),belong _,congrArg Subtype.val (based j),
    fun t => congrArg Subtype.val (real j t),Subtype.val_injective.comp (gi j),fail⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.time_orbit_range_of_meeting
#print axioms TwoAxisHelicoid.singular_component_obstructed_orbit
