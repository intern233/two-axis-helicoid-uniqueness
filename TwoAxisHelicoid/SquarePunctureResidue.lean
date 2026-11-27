import TwoAxisHelicoid.PuncturedDifferentialResidue
import TwoAxisHelicoid.ZetaRectangleResidue

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory Metric Topology
open scoped Topology Interval

/-- Along a real affine line the integral of the complex derivative of a
single-valued potential is its actual endpoint difference. Only the line
segment needs a primitive. -/
theorem complex_affine_primitive_integral {P f : ℂ → ℂ} (A B : ℂ) (a b : ℝ)
    (prim : ∀ t∈uIcc a b, HasDerivAt P (f (A+(t:ℂ)*B)) (A+(t:ℂ)*B))
    (reg : ∀ t∈uIcc a b, ContinuousAt f (A+(t:ℂ)*B)) :
    B*(∫ t in a..b, f (A+(t:ℂ)*B))=P (A+(b:ℂ)*B)-P (A+(a:ℂ)*B) := by
  let γ := fun t : ℝ => A+(t:ℂ)*B
  have dg (t : ℝ) : HasDerivAt γ B t := by
    have idr : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 t := by
      simpa only [Complex.ofReal_one] using (hasDerivAt_id' t).ofReal_comp
    simpa only [γ,one_mul] using (idr.mul_const B).const_add A
  have continuous : Continuous γ := by dsimp [γ]; fun_prop
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=P ∘ γ)
  · intro t ht
    exact ((prim t ht).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (dg t)
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    have cf : ContinuousAt (f ∘ γ) t := (reg t ht).comp (f:=γ) continuous.continuousAt
    exact ((continuousAt_const (y:=B)).mul cf).continuousWithinAt

/-- An exact complex differential integrates to zero around a square,
including when the primitive need not extend to its center. -/
theorem square_boundary_exact {f P : ℂ → ℂ} {r : ℝ}
    (h : ∀ z : ℂ, (|z.re|≤r ∧ |z.im|=r) ∨ (|z.re|=r ∧ |z.im|≤r) →
      HasDerivAt P (f z) z ∧ ContinuousAt f z) (hr : 0<r) :
    rectangleBoundary f r r=0 := by
  have iv {x : ℝ} (hx : x∈uIcc (-r) r) : |x|≤r := by
    rw [uIcc_of_le (by linarith : -r≤r)] at hx
    exact abs_le.mpr hx
  have hor (y : ℝ) (hy : |y|=r) : (∫ t in -r..r, f ((t:ℂ)+(y:ℂ)*I))=
      P ((r:ℂ)+(y:ℂ)*I)-P (-(r:ℂ)+(y:ℂ)*I) := by
    have edge (t : ℝ) (ht : t∈uIcc (-r) r) := h ((y:ℂ)*I+(t:ℂ)*1) (Or.inl (by simpa using And.intro (iv ht) hy))
    simpa only [mul_one,one_mul,Complex.ofReal_neg,add_comm ((y:ℂ)*I)] using
      complex_affine_primitive_integral ((y:ℂ)*I) 1 (-r) r (fun t ht => (edge t ht).1) (fun t ht => (edge t ht).2)
  have vert (x : ℝ) (hx : |x|=r) : I*(∫ t in -r..r, f ((x:ℂ)+(t:ℂ)*I))=
      P ((x:ℂ)+(r:ℂ)*I)-P ((x:ℂ)-(r:ℂ)*I) := by
    have edge (t : ℝ) (ht : t∈uIcc (-r) r) := h ((x:ℂ)+(t:ℂ)*I) (Or.inr (by simpa using And.intro hx (iv ht)))
    simpa only [Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using
      complex_affine_primitive_integral (x:ℂ) I (-r) r (fun t ht => (edge t ht).1) (fun t ht => (edge t ht).2)
  have top := hor r (abs_of_pos hr)
  have bot := hor (-r) (by simp [abs_of_pos hr])
  have right := vert r (abs_of_pos hr)
  have left := vert (-r) (by simp [abs_of_pos hr])
  simp only [Complex.ofReal_neg,neg_mul,← sub_eq_add_neg] at bot left
  unfold rectangleBoundary
  rw [bot,top,right,left]
  abel

/-- The same residue selected by a punctured complex primitive is detected
by every sufficiently small square. There is no meromorphic extension
assumption. -/
theorem HasPunctureResidue.small_square_integrals {f : ℂ → ℂ} {c : ℂ}
    (res : HasPunctureResidue f c) (hol : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ f z) :
    ∃ d : ℝ, 0<d ∧ ∀ r∈Ioo (0:ℝ) d, rectangleBoundary f r r=c*(2*(Real.pi:ℂ)*I) := by
  obtain ⟨P,dP⟩ := res
  obtain ⟨R,rp,good⟩ := Metric.mem_nhdsWithin_iff.mp (dP.and hol)
  refine ⟨R/3,by positivity,?_⟩
  intro r hr
  let edge := fun z : ℂ => (|z.re|≤r ∧ |z.im|=r) ∨ (|z.re|=r ∧ |z.im|≤r)
  have loc (z : ℂ) (hz : edge z) : z∈ball (0:ℂ) R ∩ {0}ᶜ := by
    have bars : |z.re|≤r ∧ |z.im|≤r := hz.elim (fun p => ⟨p.1,p.2.le⟩) (fun p => ⟨p.1.le,p.2⟩)
    constructor
    · apply mem_ball_zero_iff.mpr
      have n := Complex.norm_le_abs_re_add_abs_im z
      linarith [bars.1,bars.2,hr.2]
    · intro eq
      have ez : z=0 := eq
      subst z
      rcases hz with p|p
      · exact hr.1.ne (by simpa only [Complex.zero_im,abs_zero] using p.2)
      · exact hr.1.ne (by simpa only [Complex.zero_re,abs_zero] using p.1)
  let g := fun z : ℂ => f z-c/z
  have hreg (z : ℂ) (hz : edge z) : HasDerivAt P (g z) z ∧ ContinuousAt (fun w => f w) z := good (loc z hz) |>.imp_right DifferentiableAt.continuousAt
  have ex : rectangleBoundary g r r=0 := square_boundary_exact (P:=P) (fun z hz =>
    ⟨(hreg z hz).1,(hreg z hz).2.sub (continuousAt_const.div continuousAt_id (loc z hz).2)⟩) hr.1
  have iv {x : ℝ} (hx : x∈uIcc (-r) r) : |x|≤r := by
    rw [uIcc_of_le (by linarith [hr.1] : -r≤r)] at hx
    exact abs_le.mpr hx
  have integrable {u : ℂ → ℂ} (cu : ∀ z, edge z → ContinuousAt u z) : RectangleIntegrable u r r := by
    refine ⟨?_,?_,?_,?_⟩ <;> apply ContinuousOn.intervalIntegrable <;> intro t ht
    · exact ((cu _ (Or.inl (by simpa [abs_of_pos hr.1] using iv ht))).comp (by fun_prop)).continuousWithinAt
    · exact ((cu _ (Or.inl (by simpa [abs_of_pos hr.1] using iv ht))).comp (by fun_prop)).continuousWithinAt
    · exact ((cu _ (Or.inr (by simpa [abs_of_pos hr.1] using iv ht))).comp (by fun_prop)).continuousWithinAt
    · exact ((cu _ (Or.inr (by simpa [abs_of_pos hr.1] using iv ht))).comp (by fun_prop)).continuousWithinAt
  have cG := integrable (u:=g) (fun z hz => (hreg z hz).2.sub (continuousAt_const.div continuousAt_id (loc z hz).2))
  have cI := integrable (u:=fun z => c*z⁻¹) (fun z hz => continuousAt_const.mul (continuousAt_id.inv₀ (loc z hz).2))
  have eq : f=fun z => g z+c*z⁻¹ := by funext z; simp [g,div_eq_mul_inv]
  calc
    rectangleBoundary f r r=rectangleBoundary g r r+rectangleBoundary (fun z => c*z⁻¹) r r := by
      conv_lhs => rw [eq]
      exact rectangleBoundary_add cG cI
    _=c*rectangleBoundary (fun z : ℂ => z⁻¹) r r := by
      rw [ex,zero_add]
      simp only [rectangleBoundary,intervalIntegral.integral_const_mul]
      ring
    _=_ := by rw [rectangleBoundary_inv hr.1 hr.1]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.square_boundary_exact
#print axioms TwoAxisHelicoid.HasPunctureResidue.small_square_integrals
