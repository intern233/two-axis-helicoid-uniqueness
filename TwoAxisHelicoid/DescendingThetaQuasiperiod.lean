import TwoAxisHelicoid.KernelEllipticHeat
import TwoAxisHelicoid.SigmaAllIdentities

namespace TwoAxisHelicoid
open Complex

theorem thetaW_add_real_period (t : ℝ) (z : ℂ) : thetaW t (z+2) = thetaW t z := by
  simp only [thetaW, thetaZeta_add_two]
  ring

theorem thetaW_add_ascending_generator {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaW t (z+(1+I*t)) = thetaW t z - (Real.pi : ℂ)*I := by
  simp only [thetaW, thetaZeta_add_half_of_pos ht ht hz]
  ring

/-- The period in the descending orientation used by the original contour,
at every point off the lattice. -/
theorem thetaW_descending_quasiperiod {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaW t (z+(1-I*t)) = thetaW t z + (Real.pi : ℂ)*I := by
  let L := rhombicPeriodPair t ht
  have period : 1-I*t ∈ L.lattice := by
    have h := L.lattice.sub_mem L.ω₁_mem_lattice L.ω₂_mem_lattice
    change (2:ℂ)-(1+I*t) ∈ L.lattice at h
    rwa [show (2:ℂ)-(1+I*t)=1-I*t by ring] at h
  have shifted : z+(1-I*t) ∉ L.lattice := by
    intro h
    exact hz (by simpa only [add_sub_cancel_right] using L.lattice.sub_mem h period)
  have ascending := thetaW_add_ascending_generator ht shifted
  rw [show z+(1-I*t)+(1+I*t) = z+2 by ring, thetaW_add_real_period] at ascending
  calc
    _ = (thetaW t (z+(1-I*t))-(Real.pi : ℂ)*I)+(Real.pi : ℂ)*I := (sub_add_cancel _ _).symm
    _ = _ := congrArg (·+(Real.pi : ℂ)*I) ascending.symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaW_add_real_period
#print axioms TwoAxisHelicoid.thetaW_add_ascending_generator
#print axioms TwoAxisHelicoid.thetaW_descending_quasiperiod
