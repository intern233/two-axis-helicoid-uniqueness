import TwoAxisHelicoid.CentralHeightArcDerivative
import TwoAxisHelicoid.RegularHorizontalFiberTangent

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- Spatial velocity on any constant-height row graph in the open
quarter rectangle. The imaginary component of the Gauss map controls
the first spatial coordinate and its negative real component controls
the second, with the same strictly positive multiplier. -/
theorem quarter_row_spatial_velocity {t a s y : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    {r : ℝ → ℝ} (cont : ContinuousAt r y) (hy : y∈Ioo 0 t) (hx : r y∈Ioo (0:ℝ) 1)
    (level : ∀ᶠ u in 𝓝 y, (actualComplexHeight t a 1 ht ((r u:ℂ)+I*u)).re=s) :
    let Z := fun u : ℝ => (r u:ℂ)+I*u
    let g := thetaGauss t a 1 (Z y)
    ∃ k : ℝ, 0<k ∧ HasDerivAt (X ∘ Z) ![k*g.im,-k*g.re,0] y := by
  intro Z g
  let D := coordinateData t a 1 ht (Z y)
  let h := D 2
  have rect : Z y∈complexOpenRect 0 1 0 t := ⟨by simpa [Z] using hx,by simpa [Z] using hy⟩
  have off := rhombic_horizontal_strip_not_mem ht rect.2
  have minus : Z y-a∉(rhombicPeriodPair t ht).lattice := rhombic_horizontal_strip_not_mem ht
    (by change (Z y-a).im∈Ioo 0 t; simpa [Z] using hy)
  have plus : Z y+a∉(rhombicPeriodPair t ht).lattice := rhombic_horizontal_strip_not_mem ht
    (by change (Z y+a).im∈Ioo 0 t; simpa [Z] using hy)
  have dh : HasDerivAt (actualComplexHeight t a 1 ht) h (Z y) := actualComplexHeight_hasDerivAt ht off
  have hp : 0<h.re := by
    rw [← dh.deriv]
    exact (actual_complex_height_univalent_quarter (a:=a) ht).1 (Z y) rect
  have hn : h≠0 := fun eq => hp.ne' (congrArg re eq)
  obtain ⟨dr,_⟩ := height_row_graph_hasDerivAt cont dh hp.ne' level
  let v : ℂ := ((h.im/h.re:ℝ):ℂ)+I
  let u := normSq h/h.re
  have up : 0<u := div_pos (normSq_pos.mpr hn) hp
  have line : HasDerivAt Z v y := dr.ofReal_comp.add (by
    simpa using (hasDerivAt_id y).ofReal_comp.const_mul I)
  have step := (d _ off).comp_hasDerivAt y line
  have vh : v*h=I*(u:ℂ) := by
    apply Complex.ext <;> simp [v,u,Complex.mul_re,Complex.mul_im,Complex.normSq_apply] <;> field_simp [hp.ne'] <;> ring
  have v' : v=u • (I/h) := by
    rw [Complex.real_smul,mul_div_assoc']
    exact (eq_div_iff hn).mpr (vh.trans (mul_comm _ _))
  have typed : D=weierstrassTriple g h := coordinateData_eq_original (c:=1) ht ha off minus plus
  have tan : levelTangent D= ![((normSq g)⁻¹+1)/2*g.im,-(((normSq g)⁻¹+1)/2)*g.re,0] :=
    (congrArg levelTangent typed).trans (levelTangent_weierstrass (g:=g) hn)
  let k := ((normSq g)⁻¹+1)/2
  have kp : 0<k := div_pos (add_pos_of_nonneg_of_pos (inv_nonneg.mpr (normSq_nonneg _)) one_pos) (by norm_num)
  refine ⟨u*k,mul_pos up kp,?_⟩
  change HasDerivAt (X ∘ Z) (nullRealDerivative D v) y at step
  rw [v',map_smul,show nullRealDerivative D (I/h)=levelTangent D from rfl,tan] at step
  convert step using 1
  funext j
  fin_cases j <;> simp [k] <;> ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarter_row_spatial_velocity
