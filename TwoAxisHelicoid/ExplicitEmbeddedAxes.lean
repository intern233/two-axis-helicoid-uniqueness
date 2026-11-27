import TwoAxisHelicoid.ActualCompleteAxes
import TwoAxisHelicoid.ActualHeightSaddles
import TwoAxisHelicoid.PeriodTorusDescent
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

namespace TwoAxisHelicoid
open Complex Set
open scoped Topology

private theorem interval_inj_of_nonzero_derivative {f d : ℝ → ℝ} {l h : ℝ}
    (diff : ∀ u∈Ioo l h, HasDerivAt f (d u) u) (nz : ∀ u∈Ioo l h, d u≠0) : InjOn f (Ioo l h) := by
  have separate {a b : ℝ} (aIn : a∈Ioo l h) (bIn : b∈Ioo l h) (ab : a<b) : f a≠f b := by
    intro eq
    have inc : Icc a b⊆Ioo l h := fun _ hx => ⟨aIn.1.trans_le hx.1,hx.2.trans_lt bIn.2⟩
    obtain ⟨u,hu,zero⟩ := exists_hasDerivAt_eq_zero ab
      (fun x hx => (diff x (inc hx)).continuousAt.continuousWithinAt) eq
      (fun x hx => diff x (inc ⟨hx.1.le,hx.2.le⟩))
    exact nz u (inc ⟨hu.1.le,hu.2.le⟩) zero
  intro a ha b hb eq
  rcases lt_trichotomy a b with lt | e | gt
  · exact (separate ha hb lt eq).elim
  · exact e
  · exact (separate hb ha gt eq.symm).elim

/-- Each of the two actual straight-axis restrictions in a fundamental
domain parametrizes its entire spatial line exactly once. -/
theorem actual_axes_coordinates_bijective {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht) :
    BijOn (fun x : ℝ => X (x:ℂ) 0) (Ioo (0:ℝ) 2) univ ∧
    BijOn (fun y : ℝ => X (1+I*y) 2) (Ioo (-t) t) univ := by
  exact ⟨⟨mapsTo_univ _ _,interval_inj_of_nonzero_derivative
      (fun _ hx => actual_primitive_horizontal_hasDerivAt ht diff hx 0) (fun _ hx => coordinateData_horizontal_axis_regular ht ha hc hx),
      actual_primitive_horizontal_coordinate_surjective ht ha hc diff⟩,
    ⟨mapsTo_univ _ _,interval_inj_of_nonzero_derivative
      (fun _ hy => actual_primitive_vertical_hasDerivAt ht diff hy 2) (fun _ hy => coordinateData_vertical_axis_regular ht ha hc hy),
      actual_primitive_vertical_coordinate_surjective ht ha hc diff⟩⟩

/-- Injectivity on the union includes pairs with one parameter on each
axis. Their spatial lines meet only at the parameter represented by one. -/
theorem actual_primitive_injective_on_both_axes {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht) :
    InjOn X ((Complex.ofReal '' Ioo (0:ℝ) 2) ∪ ((fun y : ℝ => 1+I*y) '' Ioo (-t) t)) := by
  obtain ⟨H,V⟩ := actual_axes_coordinates_bijective ht ha hc diff
  have cross (x y : ℝ) (hx : x∈Ioo (0:ℝ) 2) (hy : y∈Ioo (-t) t) (e : X (x:ℂ)=X (1+I*y)) : (x:ℂ)=1+I*y := by
    have xc : x=1 := H.injOn hx (by norm_num) ((congrFun e 0).trans (actual_primitive_vertical_line ht diff hy).1)
    have yc : y=0 := V.injOn hy (show 0∈Ioo (-t) t from ⟨neg_lt_zero.mpr ht,ht⟩)
      (by simpa only [Complex.ofReal_zero,mul_zero,add_zero] using ((congrFun e 2).symm.trans (actual_primitive_horizontal_line ht diff hx).2))
    simp [xc,yc]
  rintro _ (⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩) _ (⟨u,hu,rfl⟩ | ⟨v,hv,rfl⟩) e
  · exact congrArg Complex.ofReal (H.injOn hx hu (congrFun e 0))
  · exact cross _ _ hx hv e
  · exact (cross _ _ hu hy e.symm).symm
  · exact congrArg (fun y : ℝ => (1:ℂ)+I*y) (V.injOn hy hv (congrFun e 2))

/-- Every height-critical point has one of the two specified real
representatives; the actual periodic immersion agrees there. -/
theorem actual_height_saddle_axis_representative {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z)
    {z : ℂ} (hz : z∉(rhombicPeriodPair t ht).lattice) (crit : fderiv ℝ (fun w => X w 2) z=0) :
    ∃ x∈Ioo (0:ℝ) 2, (x=a ∨ x=2-a) ∧ z-(x:ℂ)∈(rhombicPeriodPair t ht).lattice ∧ X z=X (x:ℂ) := by
  let L := rhombicPeriodPair t ht
  have same (x : ℝ) (h : z-(x:ℂ)∈L.lattice) : X z=X (x:ℂ) := by
    simpa only [show (x:ℂ)+(z-(x:ℂ))=z by ring] using per (x:ℂ) (z-(x:ℂ)) h
  rcases (actual_height_critical_iff ht ha hc diff hz).mp crit with minus | plus
  · exact ⟨a,⟨ha.1,by linarith [ha.2]⟩,Or.inl rfl,minus,same _ minus⟩
  · have trans : z-((2-a:ℝ):ℂ)∈L.lattice := by
      convert L.lattice.sub_mem plus L.ω₁_mem_lattice using 1
      change z-((2-a:ℝ):ℂ)=z+a-2
      push_cast
      ring
    exact ⟨2-a,⟨by linarith [ha.2],by linarith [ha.1]⟩,Or.inr rfl,trans,same _ trans⟩

/-- The two height saddles cannot form a spatial double point, even
before proving global injectivity of the immersion. -/
theorem distinct_height_saddles_separated {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z)
    {z w : ℂ} (hz : z∉(rhombicPeriodPair t ht).lattice) (hw : w∉(rhombicPeriodPair t ht).lattice)
    (ne : periodTorusProjection (rhombicPeriodPair t ht) z≠periodTorusProjection (rhombicPeriodPair t ht) w)
    (cz : fderiv ℝ (fun y => X y 2) z=0) (cw : fderiv ℝ (fun y => X y 2) w=0) : X z≠X w := by
  let L := rhombicPeriodPair t ht
  obtain ⟨x,hx,_,mx,ex⟩ := actual_height_saddle_axis_representative ht ha hc diff per hz cz
  obtain ⟨y,hy,_,my,ey⟩ := actual_height_saddle_axis_representative ht ha hc diff per hw cw
  intro e
  have xy : x=y := (actual_axes_coordinates_bijective ht ha hc diff).1.injOn hx hy (congrFun (ex.symm.trans (e.trans ey)) 0)
  subst y
  apply ne
  apply (periodTorusProjection_eq_iff L z w).mpr
  convert L.lattice.sub_mem my mx using 1
  abel

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_axes_coordinates_bijective
#print axioms TwoAxisHelicoid.actual_primitive_injective_on_both_axes
#print axioms TwoAxisHelicoid.distinct_height_saddles_separated
