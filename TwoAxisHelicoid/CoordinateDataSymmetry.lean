import TwoAxisHelicoid.WeierstrassCoordinateData
import TwoAxisHelicoid.ThetaADoublePeriod

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate
attribute [local irreducible] thetaA

theorem thetaA_add_lattice {t : ℝ} (ht : 0 < t) (a : ℝ) (z : ℂ)
    (w : (rhombicPeriodPair t ht).lattice) : thetaA t a (z+w) = thetaA t a z := by
  obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp w.property
  have hperiod := ((thetaA_periodic t a).int_mul m).add_period
    ((thetaA_complex_period ht a).int_mul n)
  change (m:ℂ)*2+(n:ℂ)*(1+I*t) = (w:ℂ) at he
  rw [he] at hperiod
  exact hperiod z

theorem coordinateData_add_lattice {t a c : ℝ} (ht : 0 < t) (z : ℂ)
    (w : (rhombicPeriodPair t ht).lattice) :
    coordinateData t a c ht (z+w) = coordinateData t a c ht z := by
  have hneg : thetaA t a (-(z+w)) = thetaA t a (-z) := by
    have h := thetaA_add_lattice ht a (-z) (-w)
    change thetaA t a (-z+ -(w:ℂ)) = thetaA t a (-z) at h
    simpa only [neg_add] using h
  unfold coordinateData
  rw [hneg,thetaA_add_lattice ht a z w,(rhombicPeriodPair t ht).weierstrassP_add_coe]

theorem coordinateData_neg {t a c : ℝ} (ht : 0 < t) (z : ℂ) :
    coordinateData t a c ht (-z) =
      ![coordinateData t a c ht z 0,-coordinateData t a c ht z 1,
        coordinateData t a c ht z 2] := by
  ext j
  fin_cases j <;> dsimp [coordinateData] <;>
    simp only [neg_neg,(rhombicPeriodPair t ht).weierstrassP_neg] <;> ring

theorem coordinateData_conj {t a c : ℝ} (ht : 0 < t) (z : ℂ) :
    coordinateData t a c ht (conj z) =
      ![conj (coordinateData t a c ht z 0),-conj (coordinateData t a c ht z 1),
        -conj (coordinateData t a c ht z 2)] := by
  have hreal : conj ((rhombicPeriodPair t ht).weierstrassP a) =
      (rhombicPeriodPair t ht).weierstrassP a := by
    simpa only [Complex.conj_ofReal] using (rhombic_weierstrassP_conj ht (a:ℂ)).symm
  have hneg : thetaA t a (-conj z) = conj (thetaA t a (-z)) := by
    simpa only [map_neg] using thetaA_conj t a (-z)
  ext j
  fin_cases j <;> dsimp [coordinateData] <;>
    simp only [hneg,thetaA_conj,rhombic_weierstrassP_conj,map_mul,map_add,map_sub,
      map_neg,map_div₀,map_ofNat,Complex.conj_ofReal,Complex.conj_I,hreal] <;> ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.coordinateData_add_lattice
#print axioms TwoAxisHelicoid.coordinateData_conj
