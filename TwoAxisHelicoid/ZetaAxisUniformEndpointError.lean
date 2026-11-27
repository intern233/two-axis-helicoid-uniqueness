import TwoAxisHelicoid.ZetaAxisEndpointLimits

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology Interval
attribute [local irreducible] thetaZeta zetaPoleRegular

/-- A single radius and constant control the printed ζ pole error on
the two endpoint segments. In the second inequality y is the positive
distance back from 2t; the differential in the original path is +i dy. -/
theorem zeta_axis_uniform_endpoint_errors {t : ℝ} (ht : 0 < t) :
    ∃ δ C : ℝ, 0 < δ ∧ δ < t ∧ 0 ≤ C ∧ ∀ a ∈ Ioo (0 : ℝ) δ, ∀ y ∈ Icc (0 : ℝ) δ,
      let kernel := -2*I*(a : ℂ)/((a : ℂ)^2+(y : ℂ)^2)
      ‖I*zetaAxisDifference t a y - kernel‖ ≤ C*a ∧
      ‖I*zetaAxisDifference t a (2*t-y) - kernel‖ ≤ C*a := by
  have hol := zetaPoleRegular_analyticAt ht (z := 0) (Or.inr rfl)
  obtain ⟨K,S,near,lip⟩ := hol.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨r,rpos,ball⟩ := Metric.mem_nhds_iff.mp near
  let δ := min (t/2) (min (1/2) (r/4))
  have smallT : δ ≤ t/2 := min_le_left _ _
  have smallOne : δ ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have smallR : δ ≤ r/4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,2*(K : ℝ),by dsimp [δ]; positivity,by linarith,by positivity,?_⟩
  intro a ha y hy kernel
  have aPos := ha.1
  have yNonneg := hy.1
  have aLt : a < 1 := by linarith [ha.2]
  let l : ℂ := -(a : ℂ)+(y : ℂ)*I
  let u : ℂ := (a : ℂ)+(y : ℂ)*I
  have inS (x : ℝ) (hx : |x|=a) : (x : ℂ)+(y : ℂ)*I ∈ S := by
    apply ball
    rw [Metric.mem_ball,dist_zero_right]
    calc ‖(x : ℂ)+(y : ℂ)*I‖ ≤ ‖(x : ℂ)‖+‖(y : ℂ)*I‖ := norm_add_le _ _
      _ = a+y := by simp [Real.norm_eq_abs,hx,abs_of_nonneg yNonneg]
      _ < r := by linarith [ha.2,hy.2]
  have lIn : l ∈ S := by simpa only [l,Complex.ofReal_neg] using inS (-a) (by simp [abs_of_pos aPos])
  have uIn : u ∈ S := inS a (abs_of_pos aPos)
  have hp : |a| < 1 := by simpa [abs_of_pos aPos] using aLt
  have lFree : l ∉ (rhombicPeriodPair t ht).lattice := by
    simpa only [l,Complex.ofReal_neg] using
      rhombic_noninteger_vertical_not_mem ht (x := -a) (by simpa using hp) (neg_ne_zero.mpr aPos.ne') y
  have uFree : u ∉ (rhombicPeriodPair t ht).lattice :=
    rhombic_noninteger_vertical_not_mem ht hp aPos.ne' y
  have nonzero {z : ℂ} (free : z ∉ (rhombicPeriodPair t ht).lattice) : z ≠ 0 := by
    rintro rfl
    exact free (rhombicPeriodPair t ht).lattice.zero_mem
  have principal : l⁻¹-u⁻¹ = -2*(a : ℂ)/((a : ℂ)^2+(y : ℂ)^2) := by
    calc l⁻¹-u⁻¹ = (u-l)/(l*u) := by field_simp [nonzero lFree,nonzero uFree]
      _ = _ := by
        have prod : l*u = -((a : ℂ)^2+(y : ℂ)^2) := by
          dsimp only [l,u]
          linear_combination (y : ℂ)^2 * Complex.I_sq
        rw [prod,show u-l = 2*(a : ℂ) by dsimp only [l,u]; ring,div_neg]
        ring
  have diff : zetaAxisDifference t a y =
      -2*(a : ℂ)/((a : ℂ)^2+(y : ℂ)^2) + (zetaPoleRegular t l-zetaPoleRegular t u) := by
    change thetaZeta t l-thetaZeta t u=_
    rw [thetaZeta_eq_inv_add_regular ht lFree,thetaZeta_eq_inv_add_regular ht uFree]
    linear_combination principal
  have distance : ‖l-u‖=2*a := by
    have eq : l-u = -((2*a : ℝ) : ℂ) := by dsimp only [l,u]; push_cast; ring
    simp [eq,Real.norm_eq_abs,abs_of_pos aPos]
  have bnd := lip.dist_le_mul l lIn u uIn
  simp only [dist_eq_norm,distance] at bnd
  have first : ‖I*zetaAxisDifference t a y - kernel‖ ≤ 2*(K : ℝ)*a := by
    have remainder : I*zetaAxisDifference t a y - kernel =
        I*(zetaPoleRegular t l-zetaPoleRegular t u) := by
      dsimp only [kernel]
      rw [diff]
      ring
    rw [remainder,norm_mul,Complex.norm_I,one_mul]
    calc _ ≤ (K : ℝ)*(2*a) := bnd
      _ = _ := by ring
  have paired : zetaAxisDifference t a (2*t-y)=zetaAxisDifference t a y := by
    rw [show 2*t-y = -y+2*t by ring,(zetaAxisDifference_periodic ht ⟨aPos,aLt⟩) (-y),
      zetaAxisDifference_even]
  exact ⟨first,paired.symm ▸ first⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.zeta_axis_uniform_endpoint_errors
