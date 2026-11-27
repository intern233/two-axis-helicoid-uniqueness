import TwoAxisHelicoid.FiniteWidthConformalObstruction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Bounds

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- A univalent exponential coordinate on a rectangular sector
approaching a finite circular boundary component. -/
noncomputable def annulusBoundarySector (R d : ℝ) (z : ℂ) : ℂ :=
  (R:ℂ)*Complex.exp ((d:ℂ)*(z-1))

theorem annulusBoundarySector_radius {R : ℝ} (hR : 0<R) (d : ℝ) (z : ℂ) :
    ‖annulusBoundarySector R d z‖=R*Real.exp (d*(z.re-1)) := by
  simp [annulusBoundarySector,Complex.norm_exp,Complex.mul_re,abs_of_pos hR]

theorem annulusBoundarySector_hasDerivAt (R d : ℝ) (z : ℂ) :
    HasDerivAt (annulusBoundarySector R d) (annulusBoundarySector R d z*d) z := by
  have h := ((((hasDerivAt_id z).sub_const 1).const_mul (d:ℂ)).cexp).const_mul (R:ℂ)
  simpa [annulusBoundarySector,mul_assoc] using! h

theorem annulusBoundarySector_injOn {R d : ℝ} (hR : 0<R) (hd : 0<d) (h1 : d≤1) :
    InjOn (annulusBoundarySector R d) openComplexUnitSquare := by
  have bounds (z : ℂ) (hz : z∈openComplexUnitSquare) :
      -Real.pi<((d:ℂ)*(z-1)).im ∧ ((d:ℂ)*(z-1)).im≤Real.pi := by
    have y : z.im ∈ Ioo (0:ℝ) 1 := hz.2
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.sub_im,Complex.one_im,
      sub_zero,zero_mul,add_zero]
    have upper := mul_le_mul_of_nonneg_left y.2.le hd.le
    have lower := mul_pos hd y.1
    constructor <;> linarith [Real.pi_gt_three]
  intro z hz w hw equality
  have a := bounds z hz
  have b := bounds w hw
  have e := Complex.exp_inj_of_neg_pi_lt_of_le_pi a.1 a.2 b.1 b.2
    (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hR.ne') equality)
  exact sub_left_inj.mp (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hd.ne') e)

theorem annulusBoundarySector_maps {m R : ℝ} (hR : 0<R) (hm : m<R) :
    ∃ d : ℝ, 0<d ∧ d≤1 ∧ ∀ z∈openComplexUnitSquare, m<‖annulusBoundarySector R d z‖ ∧
        ‖annulusBoundarySector R d z‖<R := by
  have cont : Continuous (fun d : ℝ => R*Real.exp (-d)) := by fun_prop
  have near : ∀ᶠ d : ℝ in 𝓝 0, m<R*Real.exp (-d) :=
    cont.continuousAt.eventually (lt_mem_nhds (by simpa using hm))
  have small : ∀ᶠ d : ℝ in 𝓝[>] 0, d∈Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  obtain ⟨d,hd,dR⟩ := (small.and (near.filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨d,hd.1,hd.2.le,?_⟩
  intro z hz
  have x : z.re∈Ioo (0:ℝ) 1 := hz.1
  rw [annulusBoundarySector_radius hR]
  constructor
  · exact dR.trans (mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by nlinarith [mul_pos hd.1 x.1])) hR)
  · simpa using (mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr
      (mul_neg_of_pos_of_neg hd.1 (sub_neg.mpr x.2))) hR)

theorem annulusBoundarySector_radius_limit {R : ℝ} (hR : 0<R) (d y : ℝ) :
    Tendsto (fun x : ℝ => ‖annulusBoundarySector R d ⟨x,y⟩‖) (𝓝[<] 1) (𝓝 R) := by
  simp only [annulusBoundarySector_radius hR]
  have h : Continuous (fun x : ℝ => R*Real.exp (d*(x-1))) := by fun_prop
  simpa using (h.continuousAt (x := 1)).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1:ℝ)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.annulusBoundarySector_injOn
#print axioms TwoAxisHelicoid.annulusBoundarySector_maps
