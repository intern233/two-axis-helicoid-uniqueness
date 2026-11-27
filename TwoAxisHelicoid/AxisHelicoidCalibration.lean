import TwoAxisHelicoid.GeometricAxisWinding
import TwoAxisHelicoid.HelicoidNormalGeometry

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate
attribute [local irreducible] thetaGauss thetaZeta thetaEtaExpression

theorem closed_actualComplexHeight_midpoint {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hG : thetaG t a = 0) :
    actualComplexHeight t a c ht (I*t) = 0 := by
  let z := I*(t : ℂ)
  have hreg := integerAxis_regular_points ht ha (show t ∈ Ioo 0 (2*t) from ⟨ht,by linarith⟩)
  have hn : -z ∉ (rhombicPeriodPair t ht).lattice := by simpa [z] using hreg.1
  have hζ := thetaZeta_add_vertical ht hn
  rw [show -z+2*I*t=z by dsimp [z]; ring,thetaZeta_neg] at hζ
  have hv : thetaZeta t z = I*((t : ℂ)*thetaEtaExpression t-Real.pi) := by
    unfold zetaImaginaryQuasi at hζ
    linear_combination hζ/2
  unfold actualComplexHeight
  rw [show I*(t : ℂ) = z from rfl,hv,closed_height_weierstrass_value ht ha hG]
  dsimp [z]
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
  ring

theorem harmonic_integer_axis_midpoint_data {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    (m : ℤ) {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    X (I*t) = 0 ∧ (thetaGauss t a m (I*t) = I ∨ thetaGauss t a m (I*t) = -I) := by
  let z := I*(t : ℂ)
  have hr := integerAxis_regular_points ht ha (show t ∈ Ioo 0 (2*t) from ⟨ht,by linarith⟩)
  have hω : -(2*z) ∈ (rhombicPeriodPair t ht).lattice := by
    apply (rhombic_mem_lattice_iff ht _).2
    refine ⟨1,-2,?_,?_⟩ <;> simp [z,Complex.mul_re,Complex.mul_im]
  have he : z+(-(2*z)) = -z := by ring
  have hper := hX.periodic z hr.1 _ hω
  rw [he,hX.neg z hr.1] at hper
  have hV := hX.vertical_axis_zero hr.1 (by simp [Complex.mul_re])
  have hheight : X z 2 = 0 := by
    have eq := congrFun hper 2
    change -X z 2 = X z 2 at eq
    linarith
  constructor
  · change X z = 0
    funext j
    fin_cases j
    · exact hV.1
    · exact hV.2
    · exact hheight
  · have hreg := (not_mem_gaussLogPoleSet _ _ _).mpr hr
    have hpd := puncturedImmersionCoefficient_periodic hX z _ hω
    rw [he] at hpd
    have hpm := congrArg nullGauss hpd
    rw [hg _ (gaussLogPoleSet_neg ht hreg),hg _ hreg] at hpm
    have heq := thetaGauss_neg_product ht a m hr.2.1 hr.2.2
    change thetaGauss t a m (-z)*thetaGauss t a m z = -1 at heq
    rw [hpm] at heq
    have hprod : (thetaGauss t a m z-I)*(thetaGauss t a m z+I)=0 := by
      calc
        _ = thetaGauss t a m z*thetaGauss t a m z-I*I := by ring
        _ = 0 := by rw [heq,Complex.I_mul_I,sub_self]
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)

noncomputable def axisHelicoidSide (g : ℂ) (α b : ℝ) (P : Fin 3 → ℝ) : ℝ :=
  let v := g * Complex.exp (I*(α*(P 2-b) : ℝ))
  v.re * P 0 + v.im * P 1

theorem axisHelicoidSide_eq_zero_iff {g : ℂ} (hg : normSq g = 1) (α b : ℝ)
    (P : Fin 3 → ℝ) : axisHelicoidSide g α b P = 0 ↔ P ∈ range (axisRuledHelicoid g α b) := by
  let v := g * Complex.exp (I*(α*(P 2-b) : ℝ))
  have hu : v.re*v.re+v.im*v.im = 1 := by
    change normSq v = 1
    rw [show v = g * Complex.exp ((α*(P 2-b) : ℝ)*I) by dsimp [v]; ring_nf,Complex.normSq_mul,
      hg,normSq_eq_norm_sq,Complex.norm_exp_ofReal_mul_I]
    norm_num
  constructor
  · intro h
    change v.re * P 0 + v.im * P 1 = 0 at h
    refine ⟨⟨P 0*v.im-P 1*v.re,P 2⟩,?_⟩
    funext j
    fin_cases j
    · change (P 0*v.im-P 1*v.re)*v.im = P 0
      linear_combination (P 0)*hu-v.re*h
    · change -(P 0*v.im-P 1*v.re)*v.re = P 1
      linear_combination (P 1)*hu-v.im*h
    · rfl
  · rintro ⟨w,rfl⟩
    simp [axisHelicoidSide,axisRuledHelicoid]
    ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_integer_axis_midpoint_data
#print axioms TwoAxisHelicoid.closed_actualComplexHeight_midpoint
#print axioms TwoAxisHelicoid.axisHelicoidSide_eq_zero_iff
