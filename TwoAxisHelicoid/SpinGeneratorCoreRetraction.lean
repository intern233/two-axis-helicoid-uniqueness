import TwoAxisHelicoid.SpinSquareFundamentalDomain
import TwoAxisHelicoid.EquivariantTorusFrame
import TwoAxisHelicoid.CompactCoreCoverTransport
import Mathlib.Topology.CompactOpen

namespace TwoAxisHelicoid
open Set Topology

noncomputable def puncturedSpinSquareProjection (L : PeriodPair) (z : SpinPuncturedSquare) : PuncturedPeriodTorus L :=
  ⟨spinSquareTorusMap L z.1,(spinSquareTorusMap_ne_zero_iff L z.1).mpr z.2⟩

theorem puncturedSpinSquareProjection_isQuotientMap (L : PeriodPair) :
    IsQuotientMap (puncturedSpinSquareProjection L) := by
  let D := ({0}ᶜ : Set (PeriodTorus L))
  have hh : {z : SpinSquare | 0 < spinSquareRadius z} = spinSquareTorusMap L ⁻¹' D :=
    Set.ext fun z => (spinSquareTorusMap_ne_zero_iff L z).symm
  let H := Homeomorph.setCongr hh
  have hq := IsQuotientMap.of_surjective_continuous (spinSquareTorusMap_surjective L) (spinSquareTorusMap_continuous L)
  exact (hq.restrictPreimage_isOpen (s := D) isOpen_compl_singleton).comp H.isQuotientMap

theorem puncturedSpinSquareFlow_same_fibers (L : PeriodPair) (t : unitInterval)
    (z w : SpinPuncturedSquare) (h : puncturedSpinSquareProjection L z = puncturedSpinSquareProjection L w) :
    puncturedSpinSquareProjection L (squareRadialFlow t z) = puncturedSpinSquareProjection L (squareRadialFlow t w) := by
  by_cases hzw : z = w
  · rw [hzw]
  have he : spinSquareTorusMap L z.1 = spinSquareTorusMap L w.1 := congrArg Subtype.val h
  have hz : SpinSquarePerimeter z.1 := by
    by_contra hn
    exact hzw (Subtype.ext (spinSquareTorusMap_injective_off_perimeter L hn he))
  have hw : SpinSquarePerimeter w.1 := by
    by_contra hn
    exact hzw (Subtype.ext (spinSquareTorusMap_injective_off_perimeter L hn he.symm).symm)
  rwa [squareRadialFlow_fixed t z hz,squareRadialFlow_fixed t w hw]

noncomputable def puncturedTorusRadialFlow (L : PeriodPair) (t : unitInterval) : PuncturedPeriodTorus L → PuncturedPeriodTorus L :=
  quotientFiberDescend _ (puncturedSpinSquareProjection_isQuotientMap L).surjective (puncturedSpinSquareProjection L ∘ squareRadialFlow t)

theorem puncturedTorusRadialFlow_proj (L : PeriodPair) (t : unitInterval) (z : SpinPuncturedSquare) :
    puncturedTorusRadialFlow L t (puncturedSpinSquareProjection L z) = puncturedSpinSquareProjection L (squareRadialFlow t z) :=
  quotientFiberDescend_apply _ _ _ (puncturedSpinSquareFlow_same_fibers L t) z

theorem puncturedTorusRadialFlow_continuous (L : PeriodPair) :
    Continuous (fun w : unitInterval × PuncturedPeriodTorus L => puncturedTorusRadialFlow L w.1 w.2) := by
  apply (puncturedSpinSquareProjection_isQuotientMap L).continuous_lift_prod_right
  simp only [puncturedTorusRadialFlow_proj]
  exact (puncturedSpinSquareProjection_isQuotientMap L).continuous.comp squareRadialFlow_continuous

theorem spinSquareTorusMap_bottom (L : PeriodPair) (x : unitInterval) : spinSquareTorusMap L (x,0) =
    (puncturedTorusGeneratorLoop L 0 x).1 := by
  change periodTorusProjection L (spinSquareLift L (x,0)) = periodTorusProjection L (periodBasisLine L 0 x)
  simp [spinSquareLift,periodBasisLine,spinSquareLinear]

theorem spinSquareTorusMap_left (L : PeriodPair) (x : unitInterval) : spinSquareTorusMap L (0,x) =
    (puncturedTorusGeneratorLoop L 1 x).1 := by
  change periodTorusProjection L (spinSquareLift L (0,x)) = periodTorusProjection L (periodBasisLine L 1 x)
  simp [spinSquareLift,periodBasisLine,spinSquareLinear]

theorem spinSquareTorusMap_top (L : PeriodPair) (x : unitInterval) : spinSquareTorusMap L (x,1) =
    (puncturedTorusGeneratorLoop L 0 x).1 := by
  rw [← spinSquareTorusMap_bottom L x]
  change periodTorusProjection L (spinSquareLift L (x,1)) = periodTorusProjection L (spinSquareLift L (x,0))
  have he : spinSquareLift L (x,1) = spinSquareLift L (x,0) + L.ω₂ := by
    simp [spinSquareLift,spinSquareLinear,add_assoc]
  rw [he,periodTorusProjection_add_lattice L _ _ L.ω₂_mem_lattice]

theorem spinSquareTorusMap_right (L : PeriodPair) (x : unitInterval) : spinSquareTorusMap L (1,x) =
    (puncturedTorusGeneratorLoop L 1 x).1 := by
  rw [← spinSquareTorusMap_left L x]
  change periodTorusProjection L (spinSquareLift L (1,x)) = periodTorusProjection L (spinSquareLift L (0,x))
  have he : spinSquareLift L (1,x) = spinSquareLift L (0,x) + L.ω₁ := by
    simp [spinSquareLift,spinSquareLinear,add_comm,add_left_comm,add_assoc]
  rw [he,periodTorusProjection_add_lattice L _ _ L.ω₁_mem_lattice]

theorem perpendicular_square_side_mem_core (L : PeriodPair) (z : SpinPuncturedSquare) (hz : SpinSquarePerimeter z.1) :
    puncturedSpinSquareProjection L z ∈ puncturedGeneratorCore L := by
  rcases z with ⟨⟨u,v⟩,hn⟩
  rcases hz with h | h | h | h
  · change u = 0 at h
    subst u
    exact Or.inr ⟨v,Subtype.ext (spinSquareTorusMap_left L v).symm⟩
  · change u = 1 at h
    subst u
    exact Or.inr ⟨v,Subtype.ext (spinSquareTorusMap_right L v).symm⟩
  · change v = 0 at h
    subst v
    exact Or.inl ⟨u,Subtype.ext (spinSquareTorusMap_bottom L u).symm⟩
  · change v = 1 at h
    subst v
    exact Or.inl ⟨u,Subtype.ext (spinSquareTorusMap_top L u).symm⟩

theorem marked_curve_has_perimeter_rep (L : PeriodPair) (x : PuncturedPeriodTorus L) (hx : x ∈ puncturedGeneratorCore L) :
    ∃ z : SpinPuncturedSquare, puncturedSpinSquareProjection L z = x ∧ SpinSquarePerimeter z.1 := by
  rcases hx with ⟨t,rfl⟩ | ⟨t,rfl⟩
  · have h : SpinSquarePerimeter (t,0) := Or.inr (Or.inr (Or.inl rfl))
    have hr := (spinSquareRadius_eq_half_iff _).mpr h
    exact ⟨⟨(t,0),by rw [hr]; norm_num⟩,Subtype.ext (spinSquareTorusMap_bottom L t),h⟩
  · have h : SpinSquarePerimeter (0,t) := Or.inl rfl
    have hr := (spinSquareRadius_eq_half_iff _).mpr h
    exact ⟨⟨(0,t),by rw [hr]; norm_num⟩,Subtype.ext (spinSquareTorusMap_left L t),h⟩

/-- The actual union of the two marked generator loops, in the actual
punctured quotient torus, is a strong deformation retract. The radial
homotopy fixes every perimeter point in a punctured fundamental square. -/
noncomputable def puncturedMarkedGeneratorRetraction (L : PeriodPair) : CoverCoreRetraction (puncturedGeneratorCore L) where
  flow := ⟨fun w => puncturedTorusRadialFlow L w.1 w.2,puncturedTorusRadialFlow_continuous L⟩
  initial x := by
    obtain ⟨z,rfl⟩ := (puncturedSpinSquareProjection_isQuotientMap L).surjective x
    change puncturedTorusRadialFlow L 0 (puncturedSpinSquareProjection L z) = _
    rw [puncturedTorusRadialFlow_proj,squareRadialFlow_zero]
  terminal x := by
    obtain ⟨z,rfl⟩ := (puncturedSpinSquareProjection_isQuotientMap L).surjective x
    change puncturedTorusRadialFlow L 1 (puncturedSpinSquareProjection L z) ∈ _
    rw [puncturedTorusRadialFlow_proj]
    exact perpendicular_square_side_mem_core L _ (squareRadialFlow_perimeter z)
  fixed t x hx := by
    obtain ⟨z,rfl,hz⟩ := marked_curve_has_perimeter_rep L x hx
    change puncturedTorusRadialFlow L t (puncturedSpinSquareProjection L z) = _
    rw [puncturedTorusRadialFlow_proj,squareRadialFlow_fixed t z hz]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.puncturedMarkedGeneratorRetraction
