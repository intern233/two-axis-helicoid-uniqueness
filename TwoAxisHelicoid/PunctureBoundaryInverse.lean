import TwoAxisHelicoid.SinglePunctureEndFlux

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Topology Interval

private def areaDet (a b : ℂ) : ℝ := a.re*b.im-a.im*b.re

private theorem period_area_ne_zero (L : PeriodPair) : areaDet L.ω₁ L.ω₂≠0 := by
  intro zero
  have re := LinearIndependent.pair_iff.mp L.indep L.ω₂.re (-L.ω₁.re) (by
    apply Complex.ext <;> simp [Complex.real_smul,Complex.mul_re,Complex.mul_im] <;> dsimp [areaDet] at zero <;> nlinarith)
  have im := LinearIndependent.pair_iff.mp L.indep L.ω₂.im (-L.ω₁.im) (by
    apply Complex.ext <;> simp [Complex.real_smul,Complex.mul_re,Complex.mul_im] <;> dsimp [areaDet] at zero <;> nlinarith)
  have non : L.ω₂≠0 := L.indep.ne_zero 1
  exact non (Complex.ext re.1 im.1)

private theorem inverse_edge_signed_area (a b : ℂ) (h : areaDet a b≠0) {r : ℝ} (hr : 0<r) :
    ∃ q : ℝ, 0<q ∧ (dilatedEdgeIntegral (fun z : ℂ => z⁻¹) a b r).im=areaDet a b*q := by
  let v := b-a
  let z := fun s : ℝ => a+(s:ℂ)*v
  have num (s : ℝ) : v.im*(z s).re-v.re*(z s).im=areaDet a b := by
    simp [z,v,areaDet,Complex.mul_re,Complex.mul_im]
    ring
  have nz (s : ℝ) : z s≠0 := fun e => h (by rw [← num s,e]; simp)
  have cz : Continuous z := by dsimp [z]; fun_prop
  let W := fun s : ℝ => (normSq (z s))⁻¹
  have cw : Continuous W := (Complex.continuous_normSq.comp cz).inv₀ (fun s => (normSq_pos.mpr (nz s)).ne')
  have ww (s : ℝ) : 0<W s := inv_pos.mpr (normSq_pos.mpr (nz s))
  refine ⟨∫ s : ℝ in 0..1, W s,intervalIntegral.integral_pos zero_lt_one cw.continuousOn
    (fun s _ => (ww s).le) ⟨0,by norm_num,ww 0⟩,?_⟩
  have F : Continuous (fun s : ℝ => v/z s) := continuous_const.div cz nz
  have eq : dilatedEdgeIntegral (fun u : ℂ => u⁻¹) a b r=∫ s : ℝ in 0..1, v/z s := by
    apply intervalIntegral.integral_congr
    intro s _
    change (r:ℂ)*v*((r:ℂ)*z s)⁻¹=v/z s
    rw [← div_eq_mul_inv,mul_div_mul_left _ _ (ofReal_ne_zero.mpr hr.ne')]
  have proj : (∫ s : ℝ in 0..1, v/z s).im=∫ s : ℝ in 0..1, (v/z s).im :=
    (Complex.imCLM.intervalIntegral_comp_comm (F.intervalIntegrable _ _)).symm
  rw [eq,proj,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  change (v/z s).im=areaDet a b*W s
  rw [Complex.div_im,← sub_div,num]
  rfl

/-- The period of dz/z over the actual puncture-centered lattice
parallelogram is nonzero for either orientation of the period basis. -/
theorem puncture_boundary_integral_inv_ne_zero (L : PeriodPair) {r : ℝ} (hr : 0<r) :
    punctureBoundaryIntegral L (fun z : ℂ => z⁻¹) r≠0 := by
  let A := spinSquareLinear L (-1/2) (-1/2)
  let B := spinSquareLinear L (1/2) (-1/2)
  let C := spinSquareLinear L (-1/2) (1/2)
  let D := spinSquareLinear L (1/2) (1/2)
  let d := areaDet L.ω₁ L.ω₂/2
  have nz : d≠0 := div_ne_zero (period_area_ne_zero L) (by norm_num)
  have areas (x y u v : ℝ) : areaDet (spinSquareLinear L x y) (spinSquareLinear L u v)=
      (x*v-y*u)*areaDet L.ω₁ L.ω₂ := by
    simp [areaDet,spinSquareLinear,Complex.real_smul,Complex.mul_re,Complex.mul_im]
    ring
  have bottom : areaDet A B=d := by rw [areas]; dsimp [d]; ring
  have right : areaDet B D=d := by rw [areas]; dsimp [d]; ring
  have top : areaDet C D= -d := by rw [areas]; dsimp [d]; ring
  have left : areaDet A C= -d := by rw [areas]; dsimp [d]; ring
  obtain ⟨p,hp,P⟩ := inverse_edge_signed_area A B (bottom.symm ▸ nz) hr
  obtain ⟨q,hq,Q⟩ := inverse_edge_signed_area B D (right.symm ▸ nz) hr
  obtain ⟨s,hs,S⟩ := inverse_edge_signed_area C D (top.symm ▸ neg_ne_zero.mpr nz) hr
  obtain ⟨u,hu,U⟩ := inverse_edge_signed_area A C (left.symm ▸ neg_ne_zero.mpr nz) hr
  intro zero
  have e := congrArg Complex.im zero
  change (_+_-_-_ : ℂ).im=0 at e
  rw [Complex.sub_im,Complex.sub_im,Complex.add_im,P,Q,S,U,bottom,right,top,left] at e
  apply (mul_ne_zero nz (by positivity : p+q+s+u≠0))
  linear_combination e

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.puncture_boundary_integral_inv_ne_zero
