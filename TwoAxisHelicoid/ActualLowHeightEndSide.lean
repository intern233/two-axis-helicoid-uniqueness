import TwoAxisHelicoid.HeightEndAxisCenter
import TwoAxisHelicoid.ExplicitMarkedReflections
import TwoAxisHelicoid.WeierstrassLogGauss

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology ComplexConjugate

/-- At large imaginary height the inverse height chart takes the entire
central line back to the physical horizontal axis. -/
theorem actual_height_inverse_horizontal_axis {t a : ℝ} (ht : 0<t) {K : ℂ → ℂ}
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z)
    (k : Tendsto K (cobounded ℂ) (𝓝[≠] 0))
    (left : ∀ᶠ z in 𝓝[≠] (0:ℂ), K (actualComplexHeight t a 1 ht z)=z)
    (right : ∀ᶠ ξ in cobounded ℂ, actualComplexHeight t a 1 ht (K ξ)=ξ) :
    ∀ᶠ ξ in cobounded ℂ, ξ.re=0 → X (K ξ) 1=X 1 1 := by
  have ck : Tendsto (fun ξ => conj (K ξ)) (cobounded ℂ) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have v := (continuous_conj.continuousAt (x:=(0:ℂ))).tendsto.comp (k.mono_right nhdsWithin_le_nhds)
      rw [map_zero] at v
      exact v
    · filter_upwards [k.eventually self_mem_nhdsWithin] with ξ hξ
      simpa using hξ
  filter_upwards [ck.eventually left,right,k.eventually (rhombic_puncture_eventually_off_lattice ht)] with ξ lk rk off
  intro zero
  have pure : -conj ξ=ξ := by apply Complex.ext <;> simp [zero]
  have id : actualComplexHeight t a 1 ht (conj (K ξ))=ξ := calc
    _ = -actualComplexHeight t a 1 ht (-conj (K ξ)) := by rw [actualComplexHeight_neg ht,neg_neg]
    _ = ξ := by rw [actualComplexHeight_reflection ht,rk,pure]
  rw [id] at lk
  have eq := congrFun (explicit_centered_primitive_reflections ht d per (K ξ) off).2 1
  change X (conj (K ξ)) 1-X 1 1= -(X (K ξ) 1-X 1 1) at eq
  rw [← lk] at eq
  linarith

/-- Uniformly for physical heights in the interval of radius one inverse angular speed, on a
far line of fixed imaginary height the transverse spatial coordinate is
strictly increasing on the positive end and strictly decreasing on the
negative end. Its sign is therefore fixed on each of the four open
half-strips. -/
theorem actual_low_height_end_transverse_order {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z) :
    let H := actualComplexHeight t a 1 ht
    ∃ (K : ℂ → ℂ) (R : ℝ), 0<R ∧ (∀ᶠ z in 𝓝[≠] (0:ℂ), K (H z)=z) ∧
      (∀ᶠ ξ in cobounded ℂ, H (K ξ)=ξ) ∧ ∀ y : ℝ, R < |y| →
        let v := fun x : ℝ => X (K ⟨x,y⟩) 1-X 1 1
        v 0=0 ∧ (0<y → StrictMonoOn v (Icc (-(1/(2*(1-a)))) (1/(2*(1-a))))) ∧
          (y<0 → StrictAntiOn v (Icc (-(1/(2*(1-a)))) (1/(2*(1-a))))) := by
  intro H
  let α := 2*(a-1)
  have na : 0< -α := by dsimp [α]; linarith [ha.2]
  have den : 0<2*(1-a) := by linarith [ha.2]
  have aa : |α|=2*(1-a) := by rw [abs_of_neg (by linarith : α<0)]; dsimp [α]; ring
  obtain ⟨K,f,R,k,hf,f0,left,coordinate,_⟩ := actual_periodic_primitive_centered_axis_end ht ha one_ne_zero d per
  have right : ∀ᶠ ξ in cobounded ℂ, H (K ξ)=ξ :=
    (tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)).mono fun ξ h => (coordinate ξ h).1
  let F := infinityCorrection f
  have small : ∀ᶠ ξ in cobounded ℂ, ‖F ξ‖<1/4 := by
    have tend : Tendsto (fun ξ => ‖F ξ‖) (cobounded ℂ) (𝓝 0) := by
      simpa only [norm_zero] using (infinityCorrection_tendsto_zero hf f0).norm
    exact tend.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/4))
  have onAxis := actual_height_inverse_horizontal_axis ht d per k left right
  obtain ⟨S,_,safe⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp (small.and onAxis)
  let B := max 1 (max (1/(-α)) (max R S))
  have bp : 0<B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have scale : 1/(-α)≤B := (le_max_left _ _).trans (le_max_right _ _)
  have bigR : R≤B := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have bigS : S≤B := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨K,B,bp,left,right,?_⟩
  intro y far v
  let J := Icc (-(1/(2*(1-a)))) (1/(2*(1-a)))
  let Z := fun x : ℝ => (⟨x,y⟩:ℂ)
  let A := fun x : ℝ => I*(α:ℂ)*Z x+F (Z x)
  have size (x : ℝ) : B<‖Z x‖ := far.trans_le (Complex.abs_im_le_norm (Z x))
  have bound (x : ℝ) := (safe (bigS.trans (size x).le)).1
  have mag : 1<(-α)*|y| := by
    have h := (div_lt_iff₀ na).mp (scale.trans_lt far)
    linarith
  have der (x : ℝ) : HasDerivAt v (Real.sinh (A x).re*Real.cos (A x).im) x := by
    have line : HasDerivAt Z 1 x := by
      have eq : Z=fun u : ℝ => (u:ℂ)+I*y := by funext u; apply Complex.ext <;> simp [Z]
      rw [eq]
      simpa using (hasDerivAt_id x).ofReal_comp.add_const (I*(y:ℂ))
    have dc := ((coordinate (Z x) (bigR.trans_lt (size x))).2.1).comp_hasDerivAt x line
    have first := (hasDerivAt_pi.mp dc 0).neg
    rw [show I*((2*(a-1)/1:ℝ):ℂ)*Z x+infinityCorrection f (Z x)=A x by simp [A,α,F],
      (weierstrass_exp_real_tangents (A x)).1] at first
    change HasDerivAt (fun u : ℝ => -((verticalRotation I (X (K (Z u))) - verticalRotation I (X 1)) 0)) _ x at first
    simpa [v,Z,Function.comp_def,verticalRotation_apply,logGaussTangentX,sub_eq_add_neg,add_comm] using first
  have cosPos (x : ℝ) (hx : x∈J) : 0<Real.cos (A x).im := by
    have fx := (Complex.abs_im_le_norm (F (Z x))).trans_lt (bound x)
    have ax : |α*x|≤1 := by
      rw [abs_mul,aa]
      have xx : |x|≤1/(2*(1-a)) := abs_le.mpr hx
      calc
        _ ≤ (2*(1-a))*(1/(2*(1-a))) := mul_le_mul_of_nonneg_left xx den.le
        _ = 1 := by rw [one_div, mul_inv_cancel₀ den.ne']
    have im : (A x).im=α*x+(F (Z x)).im := by simp [A,Z,Complex.mul_im,Complex.mul_re]
    have smallIm : |(A x).im|<5/4 := by rw [im]; linarith [abs_add_le (α*x) (F (Z x)).im]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp smallIm).1,Real.pi_gt_three],
      by linarith [(abs_lt.mp smallIm).2,Real.pi_gt_three]⟩
  have re (x : ℝ) : (A x).re= -α*y+(F (Z x)).re := by simp [A,Z,Complex.mul_re,Complex.mul_im]
  refine ⟨sub_eq_zero.mpr ((safe (bigS.trans (size 0).le)).2 rfl),?_,?_⟩
  · intro yp
    rw [abs_of_pos yp] at mag
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun x _ => (der x).continuousAt.continuousWithinAt)
    intro x hx
    have fr := (abs_lt.mp ((Complex.abs_re_le_norm (F (Z x))).trans_lt (bound x))).1
    rw [(der x).deriv]
    exact mul_pos (Real.sinh_pos_iff.mpr (by rw [re]; linarith)) (cosPos x (interior_subset hx))
  · intro yn
    rw [abs_of_neg yn] at mag
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (fun x _ => (der x).continuousAt.continuousWithinAt)
    intro x hx
    have fr := (abs_lt.mp ((Complex.abs_re_le_norm (F (Z x))).trans_lt (bound x))).2
    rw [(der x).deriv]
    exact mul_neg_of_neg_of_pos (Real.sinh_neg_iff.mpr (by rw [re]; nlinarith)) (cosPos x (interior_subset hx))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_height_inverse_horizontal_axis
#print axioms TwoAxisHelicoid.actual_low_height_end_transverse_order
