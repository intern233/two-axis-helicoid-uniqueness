import TwoAxisHelicoid.RangeDerivativeComposite
import TwoAxisHelicoid.RangeVerticalTrace
import TwoAxisHelicoid.FullPeriodBranch

namespace TwoAxisHelicoid
open Set ComplexBall
attribute [local irreducible] thetaG thetaGa thetaGt verticalA

theorem verticalA_mem_of_boundary_signs {t l u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper)
    (hl : l ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hgl : 0 < (thetaG t l).re) (hgu : (thetaG t u).re < 0) :
    verticalA t ∈ Ioo l u := by
  have ha := verticalA_spec ht
  have hz : (thetaG t (verticalA t)).re = 0 := by rw [ha.2]; rfl
  have hm := (thetaG_strictAnti_unit_of_pos ht.1).antitoneOn
  constructor
  · by_contra h
    have he := hm ha.1 hl (le_of_not_gt h)
    change (thetaG t l).re ≤ (thetaG t (verticalA t)).re at he
    linarith
  · by_contra h
    have he := hm hu ha.1 (le_of_not_gt h)
    change (thetaG t (verticalA t)).re ≤ (thetaG t u).re at he
    linarith

theorem actualPeriodAlong_deriv_lt_of_partial_bounds {t upper : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper)
    (hgt : 0 < (thetaGt t (verticalA t)).re)
    (ha : horizontalPeriodDa t (verticalA t) < 0)
    (hu : horizontalPeriodDt t (verticalA t) < upper) :
    deriv actualPeriodAlong t < upper := by
  have hb := (verticalA_spec ht).1
  have hga := thetaGa_re_neg_unit ht.1 hb.1 hb.2
  have hav : 0 < deriv verticalA t := by
    rw [(verticalA_hasDerivAt ht).deriv]
    exact div_pos_of_neg_of_neg (neg_neg_of_pos hgt) hga
  rw [(actualPeriodAlong_hasDerivAt ht).deriv]
  have hm := mul_neg_of_pos_of_neg hav ha
  linarith

theorem range_derivative_partial_upper (s : RangeCertificateSetup) (hs : s.Valid)
    {tlo thi alo ahi upperA upperT : ℚ} {N : ℕ} (hN : 0 < N)
    (p : RangeDerivativeParameters) (hp : p.Valid s tlo thi alo ahi)
    (cells : Fin N → RangeDerivativeCell) (R : ℚ)
    (hcheck : ∀ i : Fin N, (cells i).Valid s p (horizontalCellCenter (2*N) i)
      (horizontalCellRadius (2*N)) R)
    (ha : (combineHorizontalCells (fun i => (cells i).outputA.toBall s.config.prec)).center.re+
      (combineHorizontalCells (fun i => (cells i).outputA.toBall s.config.prec)).radius < upperA)
    (hu : (combineHorizontalCells (fun i => (cells i).outputT.toBall s.config.prec)).center.re+
      (combineHorizontalCells (fun i => (cells i).outputT.toBall s.config.prec)).radius < upperT)
    {t a : ℝ} (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    horizontalPeriodDa t a < (upperA : ℝ) ∧ horizontalPeriodDt t a < (upperT : ℝ) := by
  have hb := range_derivative_half_contains s hs hN p hp cells R hcheck htl htu hal hau
  constructor
  · exact (re_bounds hb.1).2.trans_lt (by exact_mod_cast ha)
  · exact (re_bounds hb.2).2.trans_lt (by exact_mod_cast hu)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.verticalA_mem_of_boundary_signs
#print axioms TwoAxisHelicoid.actualPeriodAlong_deriv_lt_of_partial_bounds
#print axioms TwoAxisHelicoid.range_derivative_partial_upper
