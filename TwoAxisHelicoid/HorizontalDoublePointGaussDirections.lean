import TwoAxisHelicoid.RegularHorizontalFiberTangent
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- If a noncentral horizontal section returns to the same spatial
point, its Gauss directions meet every line through the origin strictly
between the two parameters. The assertion concerns the actual spatial
Weierstrass tangent and uses no global embeddedness. -/
theorem horizontal_double_point_forces_all_gauss_lines {t a c s : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (hc : c≠0) {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z)
    {g : ℝ → ℂ} (cg : Continuous g) (co : ∀ y, actualComplexHeight t a c ht (g y)=⟨s,y⟩)
    (off : ∀ y, g y∉(rhombicPeriodPair t ht).lattice) (non : ∀ y, X (g y) 2≠X 1 2)
    {u v : ℝ} (uv : u<v) (same : X (g u)=X (g v)) (b : ℂ) :
    ∃ y∈Ioo u v, (conj b*thetaGauss t a 1 (g y)).re=0 := by
  let G := fun y => thetaGauss t a 1 (g y)
  let k := fun y => ((normSq (G y))⁻¹+1)/2
  let f := fun y => b.im*X (g y) 0-b.re*X (g y) 1
  have deriv (y : ℝ) : HasDerivAt f (k y*(conj b*G y).re) y := by
    have vel := (actual_regular_horizontal_fiber_tangent ht ha hc d per cg co (off y) (non y)).2
    have dx := (hasDerivAt_pi.mp vel 0).const_mul b.im
    have dy := (hasDerivAt_pi.mp vel 1).const_mul b.re
    have calcD := dx.sub dy
    change HasDerivAt f (b.im*(k y*(G y).im)-b.re*(-(k y)*(G y).re)) y at calcD
    convert calcD using 1
    simp only [Complex.mul_re,conj_re,conj_im]
    ring
  obtain ⟨y,hy,zero⟩ := exists_hasDerivAt_eq_zero uv (fun y _ => (deriv y).continuousAt.continuousWithinAt)
    (show f u=f v by simp only [f,same]) (fun y _ => deriv y)
  have kp : 0<k y := div_pos (add_pos_of_nonneg_of_pos (inv_nonneg.mpr (normSq_nonneg _)) one_pos) (by norm_num)
  exact ⟨y,hy,(mul_eq_zero.mp zero).resolve_left kp.ne'⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontal_double_point_forces_all_gauss_lines
