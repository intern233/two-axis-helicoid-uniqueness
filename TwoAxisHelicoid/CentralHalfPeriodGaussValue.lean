import TwoAxisHelicoid.CentralHalfPeriodTangent

namespace TwoAxisHelicoid
open Complex Set

theorem central_half_period_gauss_value {t a : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ha : a∈Icc (rootALower:ℝ) rootAUpper) (hp : 0<t) (ab : a∈Ioo (0:ℝ) 1) :
    thetaGauss t a 1 ((1+I*t)/2)= -I := by
  let z : ℂ := (1+I*t)/2
  let D := coordinateData t a 1 hp z
  let g := thetaGauss t a 1 z
  have hy : z.im∈Ioo 0 t := by
    simp only [z,div_ofNat_im,add_im,one_im,I_mul_im,ofReal_re,zero_add]
    exact ⟨by linarith,by linarith⟩
  have minus : z-a∉(rhombicPeriodPair t hp).lattice := rhombic_horizontal_strip_not_mem hp
    (by change (z-a).im∈Ioo 0 t; simpa only [sub_im,ofReal_im,sub_zero] using hy)
  have plus : z+a∉(rhombicPeriodPair t hp).lattice := rhombic_horizontal_strip_not_mem hp
    (by change (z+a).im∈Ioo 0 t; simpa only [add_im,ofReal_im,add_zero] using hy)
  have typed : D=weierstrassTriple g (D 2) := coordinateData_eq_original hp ab (rhombic_horizontal_strip_not_mem hp hy) minus plus
  have eq : D 0+I*D 1= -g*(D 2) := by
    have e0 := congrFun typed 0
    have e1 := congrFun typed 1
    change D 0=(g⁻¹-g)/2*(D 2) at e0
    change D 1=I*(g⁻¹+g)/2*(D 2) at e1
    rw [e0,e1]
    linear_combination (g⁻¹+g)*(D 2)/2*I_sq
  obtain ⟨positive,dx,dy,_⟩ := central_half_period_tangent_orientation ht ha hp ab
  change D 0=I*(D 2) at dx
  change D 1=0 at dy
  change 3<(D 2).re at positive
  have nonzero : D 2≠0 := fun e => (by rw [e,zero_re] at positive; linarith)
  rw [dx,dy,mul_zero,add_zero] at eq
  change g= -I
  exact neg_injective (by rw [neg_neg]; exact ((mul_left_inj' nonzero).mp eq).symm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_half_period_gauss_value
