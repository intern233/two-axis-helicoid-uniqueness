import TwoAxisHelicoid.HolomorphicNullImmersion
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff

/-- The coupled linearization records the difference between two sheets
and the height on the first sheet. -/
noncomputable def doublePointHeightDerivative (A B : ℂ →L[ℝ] (Fin 3 → ℝ)) :
    (ℂ × ℂ) →L[ℝ] ((Fin 3 → ℝ) × ℝ) :=
  let a := A.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)
  let b := B.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)
  (a-b).prod ((ContinuousLinearMap.proj 2).comp a)

/-- At an intersection of locally maximal height the coupled derivative is
singular. A submersion would realize higher intersections nearby. -/
theorem height_maximal_double_point_not_surjective (X Y : ℂ → Fin 3 → ℝ) {z w : ℂ}
    (hX : ContDiffAt ℝ 1 X z) (hY : ContDiffAt ℝ 1 Y w) (eq : X z=Y w)
    (maximal : ∀ᶠ q : ℂ × ℂ in 𝓝 (z,w), X q.1=Y q.2 → X q.1 2 ≤ X z 2) :
    ¬ Function.Surjective (doublePointHeightDerivative (fderiv ℝ X z) (fderiv ℝ Y w)) := by
  let F := fun q : ℂ × ℂ => (X q.1-Y q.2,X q.1 2)
  let J := doublePointHeightDerivative (fderiv ℝ X z) (fderiv ℝ Y w)
  have a := (hX.hasStrictFDerivAt one_ne_zero).comp (z,w) (ContinuousLinearMap.fst ℝ ℂ ℂ).hasStrictFDerivAt
  have b := (hY.hasStrictFDerivAt one_ne_zero).comp (z,w) (ContinuousLinearMap.snd ℝ ℂ ℂ).hasStrictFDerivAt
  have d : HasStrictFDerivAt F J (z,w) :=
    (a.sub b).prodMk ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).hasStrictFDerivAt.comp (z,w) a)
  intro sur
  let S := {q : ℂ × ℂ | X q.1=Y q.2 → X q.1 2 ≤ X z 2}
  have mem : F '' S ∈ 𝓝 (0,X z 2) := by
    have e : F (z,w)=(0,X z 2) := Prod.ext (sub_eq_zero.mpr eq) rfl
    rw [← e,← d.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr sur)]
    exact image_mem_map maximal
  have line : ContinuousAt (fun h : ℝ => ((0 : Fin 3 → ℝ),h)) (X z 2) :=
    continuousAt_const.prodMk continuousAt_id
  have nearby : ∀ᶠ h in 𝓝[>] (X z 2), ((0 : Fin 3 → ℝ),h) ∈ F '' S := nhdsWithin_le_nhds (s := Ioi (X z 2)) (line mem)
  obtain ⟨h,hh,up⟩ := (nearby.and (self_mem_nhdsWithin : ∀ᶠ h in 𝓝[>] (X z 2), X z 2<h)).exists
  obtain ⟨q,hq,he⟩ := hh
  have same : X q.1=Y q.2 := sub_eq_zero.mp (congrArg Prod.fst he)
  have height : X q.1 2=h := congrArg Prod.snd he
  exact up.not_ge (height.ge.trans (hq same))

/-- Horizontal tangent obtained by lifting unit imaginary height speed. -/
noncomputable def levelTangent (p : Fin 3 → ℂ) : Fin 3 → ℝ :=
  nullRealDerivative p (I/p 2)

private theorem horizontal_parameter {u h : ℂ} (hh : h≠0) (hu : (u*h).re=0) :
    u=(u*h).im • (I/h) := by
  rw [Complex.real_smul,← mul_div_assoc,eq_div_iff hh]
  simpa only [hu,Complex.ofReal_zero,zero_add] using (Complex.re_add_im (u*h)).symm

/-- If both heights are regular and the horizontal tangent vectors are
independent, the difference-and-height derivative is onto. -/
theorem double_point_height_surjective_of_level_det {p q : Fin 3 → ℂ}
    (hp : p 2≠0) (hq : q 2≠0)
    (det : levelTangent p 0*levelTangent q 1-levelTangent p 1*levelTangent q 0≠0) :
    Function.Surjective (doublePointHeightDerivative (nullRealDerivative p) (nullRealDerivative q)) := by
  let J := doublePointHeightDerivative (nullRealDerivative p) (nullRealDerivative q)
  have finite : Module.finrank ℝ (ℂ × ℂ)=Module.finrank ℝ ((Fin 3 → ℝ) × ℝ) := by
    simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := J.toLinearMap) finite).mp
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨u,v⟩ eq
  have equal : nullRealDerivative p u=nullRealDerivative q v := sub_eq_zero.mp (congrArg Prod.fst eq)
  have uz : (u*p 2).re=0 := congrArg Prod.snd eq
  have vz : (v*q 2).re=0 := (congrFun equal 2).symm.trans uz
  let a := (u*p 2).im
  let b := (v*q 2).im
  have eu : u=a • (I/p 2) := horizontal_parameter hp uz
  have ev : v=b • (I/q 2) := horizontal_parameter hq vz
  have lin : a • levelTangent p=b • levelTangent q := by
    rw [eu,ev,map_smul,map_smul] at equal
    exact equal
  have x : a*levelTangent p 0=b*levelTangent q 0 := congrFun lin 0
  have y : a*levelTangent p 1=b*levelTangent q 1 := congrFun lin 1
  have az : a=0 := (mul_eq_zero.mp (show a*(levelTangent p 0*levelTangent q 1-levelTangent p 1*levelTangent q 0)=0 by
    linear_combination levelTangent q 1*x-levelTangent q 0*y)).resolve_right det
  have bz : b=0 := (mul_eq_zero.mp (show b*(levelTangent p 0*levelTangent q 1-levelTangent p 1*levelTangent q 0)=0 by
    linear_combination levelTangent p 1*x-levelTangent p 0*y)).resolve_right det
  exact Prod.ext (eu.trans (az ▸ zero_smul _ _)) (ev.trans (bz ▸ zero_smul _ _))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.height_maximal_double_point_not_surjective
#print axioms TwoAxisHelicoid.double_point_height_surjective_of_level_det
