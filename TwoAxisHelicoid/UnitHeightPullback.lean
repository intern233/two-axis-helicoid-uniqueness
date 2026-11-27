import TwoAxisHelicoid.HolomorphicImmersionCoordinateChange
import TwoAxisHelicoid.NullCoordinateRecognition

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology

/-- In any complex coordinate inverse to the actual height primitive
the height coefficient is exactly one. The Gauss map is unchanged,
including when a winding power is present at infinity. -/
theorem inverse_height_pullback_weierstrass {X : ℂ → Fin 3 → ℝ} {K H : ℂ → ℂ} {w : ℂ}
    (reg : DifferentiableAt ℝ X (K w)) (conf : ConformalCoordinateDerivatives X (K w))
    (k : DifferentiableAt ℂ K w) (prim : HasDerivAt H (immersionComplexCoefficient X (K w) 2) (K w))
    (inverse : H ∘ K=ᶠ[𝓝 w] id) :
    HasFDerivAt (X ∘ K) (nullRealDerivative (weierstrassTriple (immersionGaussMap X (K w)) 1)) w ∧
      immersionGaussMap (X ∘ K) w=immersionGaussMap X (K w) := by
  let p := immersionComplexCoefficient X (K w)
  let q := immersionComplexCoefficient (X ∘ K) w
  let d := deriv K w
  have hd : p 2*d=1 := (prim.comp w k.hasDerivAt).deriv.symm.trans (inverse.deriv_eq.trans (by simp))
  have dn : d≠0 := fun h => one_ne_zero (hd.symm.trans (by rw [h,mul_zero]))
  have transform (j : Fin 3) : q j=d*p j := immersionComplexCoefficient_comp_holomorphic reg k.hasDerivAt j
  have null : ComplexNull q := by
    have n : ComplexNull p := immersionComplexCoefficient_null conf
    change (q 0)^2+(q 1)^2+(q 2)^2=0
    rw [transform,transform,transform]
    dsimp only [ComplexNull] at n
    linear_combination d^2*n
  have unit : q 2=1 := (transform 2).trans ((mul_comm _ _).trans hd)
  have gauss := immersionGaussMap_comp_holomorphic reg k.hasDerivAt dn
  have eq : q=weierstrassTriple (immersionGaussMap X (K w)) 1 := by
    calc q = weierstrassTriple (nullGauss q) (q 2) := null_eq_weierstrassTriple null (unit.trans_ne one_ne_zero)
         _ = _ := by rw [unit,show nullGauss q=immersionGaussMap X (K w) from gauss]
  exact ⟨eq ▸ (immersionComplexCoefficient_hasFDerivAt (reg.comp w (k.restrictScalars ℝ))),gauss⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.inverse_height_pullback_weierstrass
