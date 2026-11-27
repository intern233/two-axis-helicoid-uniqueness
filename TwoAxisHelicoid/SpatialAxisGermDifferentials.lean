import TwoAxisHelicoid.RealCoefficientSymmetry
import TwoAxisHelicoid.NullGaussSymmetry
import TwoAxisHelicoid.HolomorphicImmersionCoordinateChange
import TwoAxisHelicoid.SimilaritySymmetry

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate

private theorem scaled_germ_coefficient {f g : ℂ → ℝ} {z : ℂ} (s : ℝ)
    (df : DifferentiableAt ℝ f z) (dg : DifferentiableAt ℝ g z) (eq : g =ᶠ[𝓝 z] fun w => s*f w) :
    scalarComplexCoefficient g z=(s:ℂ)*scalarComplexCoefficient f z :=
  realCoefficientDerivative_injective <| (scalarComplexCoefficient_hasFDerivAt dg).unique
    ((real_primitive_scalar_mul_derivative (scalarComplexCoefficient_hasFDerivAt df) s).congr_of_eventuallyEq eq)

private theorem conjugated_argument_coefficient {f : ℂ → ℝ} {z : ℂ} (df : DifferentiableAt ℝ f (conj z)) :
    scalarComplexCoefficient (fun w => f (conj w)) z=conj (scalarComplexCoefficient f (conj z)) := by
  have d := (scalarComplexCoefficient_hasFDerivAt df).comp z Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  rw [realCoefficientDerivative_conjugation] at d
  exact realCoefficientDerivative_injective ((scalarComplexCoefficient_hasFDerivAt d.differentiableAt).unique d)

/-- In any puncture chart, the orientation-preserving composition of
the two spatial half turns negates the height differential and inverts
the Gauss map (with multiplier minus one). -/
theorem physical_axis_product_germ {Y : ℂ → Fin 3 → ℝ} {u : ℂ → ℂ} {z : ℂ}
    (dy : DifferentiableAt ℝ Y z) (dyu : DifferentiableAt ℝ Y (u z))
    (du : DifferentiableAt ℂ u z) (unit : deriv u z≠0)
    (null : ComplexNull (immersionComplexCoefficient Y z)) (hn : immersionComplexCoefficient Y z 2≠0)
    (space : (Y ∘ u) =ᶠ[𝓝 z] (halfTurnX ∘ halfTurnZ ∘ Y)) :
    deriv u z*immersionComplexCoefficient Y (u z) 2= -immersionComplexCoefficient Y z 2 ∧
      immersionGaussMap Y (u z)*immersionGaussMap Y z= -1 := by
  let p := immersionComplexCoefficient Y z
  let q := immersionComplexCoefficient (Y ∘ u) z
  have comp := dyu.comp z (du.restrictScalars ℝ)
  have rows (j : Fin 3) : q j=((![-1,1,-1] : Fin 3 → ℝ) j : ℂ)*p j := by
    apply scaled_germ_coefficient _ (differentiableAt_pi.mp dy j) (differentiableAt_pi.mp comp j)
    filter_upwards [space] with w e
    have ej := congrFun e j
    fin_cases j <;> simpa [Function.comp_def,halfTurnX,halfTurnZ] using ej
  have val : q= ![-p 0,p 1,-p 2] := by
    funext j
    have eq := rows j
    fin_cases j <;> simpa using eq
  have minus : nullHorizontalMinus q= -(nullHorizontalPlus p) := by
    rw [val]
    change -p 0-I*p 1= -(p 0+I*p 1)
    ring
  refine ⟨(immersionComplexCoefficient_comp_holomorphic dyu du.hasDerivAt 2).symm.trans (by change q 2= -p 2; rw [val]; rfl),?_⟩
  rw [← immersionGaussMap_comp_holomorphic dyu du.hasDerivAt unit]
  change (q 2/nullHorizontalMinus q)*nullGauss p= -1
  rw [minus,show q 2= -p 2 from congrFun val 2,neg_div_neg_eq]
  exact null_gauss_opposite_product null hn

/-- The horizontal half turn, expressed by an antiholomorphic end
germ, negates the conjugated height differential and the conjugated
Gauss map in the original coordinates. -/
theorem physical_horizontal_reflection_germ {Y : ℂ → Fin 3 → ℝ} {v : ℂ → ℂ} {z : ℂ}
    (dy : DifferentiableAt ℝ Y (conj z)) (dyv : DifferentiableAt ℝ Y (v z))
    (dv : DifferentiableAt ℂ v z) (unit : deriv v z≠0)
    (space : (Y ∘ v) =ᶠ[𝓝 z] (halfTurnX ∘ Y ∘ conj)) :
    deriv v z*immersionComplexCoefficient Y (v z) 2= -conj (immersionComplexCoefficient Y (conj z) 2) ∧
      immersionGaussMap Y (v z)= -conj (immersionGaussMap Y (conj z)) := by
  let p := immersionComplexCoefficient Y (conj z)
  let q := immersionComplexCoefficient (Y ∘ v) z
  have comp := dyv.comp z (dv.restrictScalars ℝ)
  have rows (j : Fin 3) : q j=((![1,-1,-1] : Fin 3 → ℝ) j : ℂ)*conj (p j) := by
    have df := differentiableAt_pi.mp dy j
    change q j=((![1,-1,-1] : Fin 3 → ℝ) j : ℂ)*conj (scalarComplexCoefficient (fun w => Y w j) (conj z))
    rw [← conjugated_argument_coefficient df]
    apply scaled_germ_coefficient _ (df.comp z Complex.conjCLE.toContinuousLinearMap.differentiableAt) (differentiableAt_pi.mp comp j)
    filter_upwards [space] with w e
    have ej := congrFun e j
    fin_cases j <;> simpa [Function.comp_def,halfTurnX] using ej
  have val : q= ![conj (p 0),-conj (p 1),-conj (p 2)] := by
    funext j
    have eq := rows j
    fin_cases j <;> simpa using eq
  refine ⟨(immersionComplexCoefficient_comp_holomorphic dyv dv.hasDerivAt 2).symm.trans (congrFun val 2),?_⟩
  rw [← immersionGaussMap_comp_holomorphic dyv dv.hasDerivAt unit]
  change nullGauss q= -conj (nullGauss p)
  simp [val,nullGauss,nullHorizontalMinus,map_div₀,map_sub,map_mul,neg_div]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_axis_product_germ
#print axioms TwoAxisHelicoid.physical_horizontal_reflection_germ
