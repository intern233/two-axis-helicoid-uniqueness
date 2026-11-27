import TwoAxisHelicoid.WeierstrassScaling
import TwoAxisHelicoid.SigmaAllPositive

namespace TwoAxisHelicoid
open Complex Set

/-- The full periods (2ω₁, 2ω₃) of Bobenko §6, with (L=2A) and
(t=B/A). Their sum is the real full period (2L). -/
noncomputable def bobenkoPeriodPair (t L : ℝ) (ht : 0 < t) (hL : 0 < L) : PeriodPair where
  ω₁ := L*(1-I*t)
  ω₂ := L*(1+I*t)
  indep := by
    apply LinearIndependent.pair_iff.mpr
    intro x y h
    have scalar : (x : ℂ)*((L:ℂ)*(1-I*t)) + (y:ℂ)*(L*(1+I*t)) = 0 := by
      simpa only [Complex.real_smul] using h
    have unscaled : x • (rhombicPeriodPair t ht).ω₁ + (y-x) • (rhombicPeriodPair t ht).ω₂ = 0 := by
      apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hL.ne' : (L : ℂ) ≠ 0)
      simp only [mul_zero,Complex.real_smul,rhombicPeriodPair,Complex.ofReal_sub]
      linear_combination scalar
    obtain ⟨hx,hy⟩ := (LinearIndependent.pair_iff.mp (rhombicPeriodPair t ht).indep) x (y-x) unscaled
    exact ⟨hx,by linarith⟩

theorem bobenko_lattice_scale_iff {t L : ℝ} (ht : 0 < t) (hL : 0 < L) (z : ℂ) :
    L*z ∈ (bobenkoPeriodPair t L ht hL).lattice ↔ z ∈ (rhombicPeriodPair t ht).lattice := by
  constructor
  · rintro h
    obtain ⟨m,n,eq⟩ := PeriodPair.mem_lattice.mp h
    refine PeriodPair.mem_lattice.mpr ⟨m,n-m,?_⟩
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hL.ne' : (L:ℂ) ≠ 0)
    change (m:ℂ)*(L*(1-I*t)) + (n:ℂ)*(L*(1+I*t)) = L*z at eq
    change (L:ℂ)*((m:ℂ)*2+((n-m : ℤ):ℂ)*(1+I*t)) = L*z
    push_cast
    linear_combination eq
  · rintro h
    obtain ⟨m,n,eq⟩ := PeriodPair.mem_lattice.mp h
    refine PeriodPair.mem_lattice.mpr ⟨m,m+n,?_⟩
    change (m:ℂ)*2+(n:ℂ)*(1+I*t)=z at eq
    change (m:ℂ)*(L*(1-I*t)) + ((m+n : ℤ):ℂ)*(L*(1+I*t)) = L*z
    push_cast
    linear_combination (L:ℂ)*eq

noncomputable def bobenkoLatticeEquiv (t L : ℝ) (ht : 0 < t) (hL : 0 < L) :
    (rhombicPeriodPair t ht).lattice ≃ (bobenkoPeriodPair t L ht hL).lattice where
  toFun z := ⟨L*(z:ℂ),(bobenko_lattice_scale_iff ht hL _).mpr z.2⟩
  invFun w := ⟨(w:ℂ)/L,(bobenko_lattice_scale_iff ht hL _).mp (by
    rw [show (L:ℂ)*((w:ℂ)/L) = w by field_simp [Complex.ofReal_ne_zero.mpr hL.ne']]
    exact w.2)⟩
  left_inv z := by apply Subtype.ext; change (L:ℂ)*(z:ℂ)/L=z; field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  right_inv w := by apply Subtype.ext; change (L:ℂ)*((w:ℂ)/L)=w; field_simp [Complex.ofReal_ne_zero.mpr hL.ne']

theorem bobenko_weierstrassP_scale {t L : ℝ} (ht : 0 < t) (hL : 0 < L) (z : ℂ) :
    (bobenkoPeriodPair t L ht hL).weierstrassP (L*z) =
      ((L:ℂ)^2)⁻¹ * (rhombicPeriodPair t ht).weierstrassP z :=
  weierstrassP_equiv_scale _ _ _ (bobenkoLatticeEquiv t L ht hL) (fun _ => rfl) z

/-- Sigma and zeta in the physical (w)-coordinate. Their derivatives
and their normalization at the origin are recorded below. -/
noncomputable def bobenkoSigma (t L : ℝ) (w : ℂ) : ℂ := L * thetaSigma t (w / L)
noncomputable def bobenkoZeta (t L : ℝ) (w : ℂ) : ℂ := thetaZeta t (w / L) / L

theorem bobenko_sigma_scale {t L : ℝ} (hL : 0 < L) (z : ℂ) :
    bobenkoSigma t L (L*z) = L*thetaSigma t z := by
  unfold bobenkoSigma
  rw [show (L:ℂ)*z/L = z by field_simp [Complex.ofReal_ne_zero.mpr hL.ne']]

theorem bobenko_zeta_scale {t L : ℝ} (hL : 0 < L) (z : ℂ) :
    bobenkoZeta t L (L*z) = thetaZeta t z/L := by
  unfold bobenkoZeta
  rw [show (L:ℂ)*z/L = z by field_simp [Complex.ofReal_ne_zero.mpr hL.ne']]

theorem bobenko_sigma_zero_iff {t L : ℝ} (ht : 0 < t) (hL : 0 < L) (w : ℂ) :
    bobenkoSigma t L w = 0 ↔ w ∈ (bobenkoPeriodPair t L ht hL).lattice := by
  let z := w / (L:ℂ)
  have eq : (L:ℂ)*z = w := by dsimp [z]; field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  rw [← eq,bobenko_sigma_scale hL,mul_eq_zero,thetaSigma_zero_iff_lattice_of_pos ht ht,
    bobenko_lattice_scale_iff ht hL]
  simp [Complex.ofReal_ne_zero.mpr hL.ne']

theorem bobenko_sigma_normalization {t L : ℝ} (ht : 0 < t) (hL : 0 < L) :
    HasDerivAt (bobenkoSigma t L) 1 0 := by
  have inv := (hasDerivAt_id (0:ℂ)).div_const (L:ℂ)
  have base : HasDerivAt (thetaSigma t) 1 (0/(L:ℂ)) := by simpa using thetaSigma_hasDerivAt_zero_of_pos ht
  convert (base.comp 0 inv).const_mul (L:ℂ) using 1 <;>
    first | rfl | field_simp [Complex.ofReal_ne_zero.mpr hL.ne']

theorem bobenko_zeta_derivative {t L : ℝ} (ht : 0 < t) (hL : 0 < L) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    HasDerivAt (bobenkoZeta t L) (-(bobenkoPeriodPair t L ht hL).weierstrassP (L*z)) (L*z) := by
  have divL : (L:ℂ)*z/L = z := by field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  have base : HasDerivAt (thetaZeta t) (-(rhombicPeriodPair t ht).weierstrassP z) ((L:ℂ)*z/L) := by
    rw [divL]
    exact thetaZeta_hasDerivAt_of_pos ht ht hz
  have inv := (hasDerivAt_id ((L:ℂ)*z)).div_const (L:ℂ)
  rw [bobenko_weierstrassP_scale ht hL]
  convert ((base.comp (h := fun w : ℂ => w / (L : ℂ)) ((L : ℂ)*z) inv).div_const (L:ℂ)) using 1 <;>
    first | rfl | field_simp [Complex.ofReal_ne_zero.mpr hL.ne']

/-- Pullback of (2ab) in the proof of (39), Bobenko p.25. -/
theorem bobenko_height_coefficient_pullback {t L a : ℝ} (ht : 0 < t) (hL : 0 < L)
    (ha : a = 1 - 1/(2*L)) (z : ℂ) :
    (L:ℂ) * (2*I*((bobenkoPeriodPair t L ht hL).weierstrassP (1/2-L) -
      (bobenkoPeriodPair t L ht hL).weierstrassP (L*z))) =
    I*(-2/L)*((rhombicPeriodPair t ht).weierstrassP z - (rhombicPeriodPair t ht).weierstrassP a) := by
  have val : (1/2-L : ℂ) = L*(-(a:ℂ)) := by
    rw [ha]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
    ring
  rw [val,bobenko_weierstrassP_scale ht hL,bobenko_weierstrassP_scale ht hL,PeriodPair.weierstrassP_neg]
  field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.bobenko_lattice_scale_iff
#print axioms TwoAxisHelicoid.bobenko_sigma_normalization
#print axioms TwoAxisHelicoid.bobenko_zeta_derivative
#print axioms TwoAxisHelicoid.bobenko_height_coefficient_pullback
