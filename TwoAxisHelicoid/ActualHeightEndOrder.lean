import TwoAxisHelicoid.WeierstrassCoordinateData
import Mathlib.Analysis.Meromorphic.Order

namespace TwoAxisHelicoid
open Complex Set

/-- The explicit third coordinate differential has exactly a double pole,
for every nonzero real scale and every parameter; subtracting its interior
Weierstrass value does not change the order at the puncture. -/
theorem actual_coordinate_height_double_pole {t a c : ℝ} (ht : 0 < t) (hc : c ≠ 0) :
    meromorphicOrderAt (fun z => coordinateData t a c ht z 2) 0 = (-2:ℤ) := by
  let L := rhombicPeriodPair t ht
  let b : ℂ → ℂ := fun _ => -L.weierstrassP a
  let k : ℂ := I*(c:ℂ)
  have hk : k ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc)
  have hp := L.order_weierstrassP 0 L.lattice.zero_mem
  have hlt : meromorphicOrderAt L.weierstrassP 0 < meromorphicOrderAt b 0 := by
    apply lt_of_lt_of_le _ (show 0 ≤ meromorphicOrderAt b 0 from analyticAt_const.meromorphicOrderAt_nonneg)
    rw [hp]
    exact WithTop.coe_lt_coe.mpr (by decide : (-2:ℤ) < 0)
  have hsum := meromorphicOrderAt_add_eq_left_of_lt (show MeromorphicAt b 0 from analyticAt_const.meromorphicAt) hlt
  have he : (fun z => coordinateData t a c ht z 2) = (fun _ : ℂ => k)*(L.weierstrassP+b) := by
    funext z
    change I*(c:ℂ)*(L.weierstrassP z-L.weierstrassP a) = k*(L.weierstrassP z-L.weierstrassP a)
    rfl
  rw [he,meromorphicOrderAt_mul analyticAt_const.meromorphicAt ((L.meromorphic_weierstrassP 0).add analyticAt_const.meromorphicAt),meromorphicOrderAt_const,ite_eq_right hk,zero_add,hsum,hp]
  decide

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_coordinate_height_double_pole
