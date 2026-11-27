import TwoAxisHelicoid.SpatialConormalFlux
import TwoAxisHelicoid.OriginalCoordinatePeriods
import TwoAxisHelicoid.TorusSpatialConormalFlux

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology Interval

/-- The imaginary period vector of one actual arc commutes with any
real linear coordinate map for which the resulting parameter remains
conformal. In particular this covers all spatial similarities, of
either orientation, with exactly the same marked curve. -/
theorem ComplexPeriodArc.affine_spatial_flux {Ω : Set ℂ} (A : ComplexPeriodArc Ω)
    (p : ℂ → Fin 3 → ℂ) (pc : ∀ j, ContinuousOn (fun z => p z j) Ω)
    {Z : ℂ → Fin 3 → ℝ} (T : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (dz : ∀ z∈Ω, HasFDerivAt Z (T.comp (nullRealDerivative (p z))) z)
    (null : ∀ z∈Ω, ConformalCoordinateDerivatives Z z) (j : Fin 3) :
    A.spatialConormalFlux Z j = T (fun k => (A.integral (fun z => p z k)).im) j := by
  let J := fun s : ℝ => fun k : Fin 3 => (A.velocity s*p (A.curve s) k).im
  have cC (k : Fin 3) : ContinuousOn (fun s => A.velocity s*p (A.curve s) k) (Icc A.left A.right) :=
    A.continuous_velocity.mul ((pc k).comp A.continuous_curve A.stays)
  have cj : ContinuousOn J (Icc A.left A.right) := continuousOn_pi.mpr fun k => continuous_im.comp_continuousOn (cC k)
  have integr : IntervalIntegrable J volume A.left A.right := cj.intervalIntegrable_of_Icc A.ordered
  have value : (∫ s in A.left..A.right, J s)=fun k => (A.integral (fun z => p z k)).im := by
    funext k
    let l : (Fin 3 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
    have ev := l.intervalIntegral_comp_comm integr
    exact ev.symm.trans (Complex.imCLM.intervalIntegral_comp_comm ((cC k).intervalIntegrable_of_Icc A.ordered))
  let l := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).comp T
  rw [← value]
  change _=l (∫ s in A.left..A.right, J s)
  rw [← l.intervalIntegral_comp_comm integr]
  apply intervalIntegral.integral_congr
  intro s hs
  have off := A.stays (by simpa only [uIcc_of_le A.ordered] using hs)
  let z := A.curve s
  let q := immersionComplexCoefficient Z z
  have hq : HasFDerivAt Z (nullRealDerivative q) z :=
    immersionComplexCoefficient_hasFDerivAt (dz z off).differentiableAt
  have density := chartRightUnitConormal_density (immersionComplexCoefficient_null (null z off)) hq (A.velocity s) j
  change ‖fderiv ℝ (coordinateToEuclidean ∘ Z) z (A.velocity s)‖ * (chartRightUnitConormal Z z (A.velocity s)) j=T (J s) j
  rw [density]
  have v : nullRealDerivative q (-I*A.velocity s)=T (nullRealDerivative (p z) (-I*A.velocity s)) :=
    congrArg (fun D : ℂ →L[ℝ] (Fin 3 → ℝ) => D (-I*A.velocity s)) (hq.unique (dz _ off))
  have turn (a b : ℂ) : ((-I*a)*b).re=(a*b).im := by rw [mul_assoc]; simp [Complex.mul_re]
  have jv : nullRealDerivative (p z) (-I*A.velocity s)=J s := funext fun k => turn _ _
  rw [jv] at v
  exact (turn _ _).symm.trans (congrFun v j)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ComplexPeriodArc.affine_spatial_flux
