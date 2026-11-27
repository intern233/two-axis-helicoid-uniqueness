import TwoAxisHelicoid.StripPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology

/-- Complex period on the positively oriented circle of radius r. -/
noncomputable def exteriorAngularPeriod (f : ℂ → ℂ) (r : ℝ) : ℂ :=
  I*(∫ θ : ℝ in 0..2*Real.pi, ((r:ℂ)*exp ((θ:ℂ)*I))*f ((r:ℂ)*exp ((θ:ℂ)*I)))

private theorem right_half_plane_primitive {f : ℂ → ℂ} {l : ℝ}
    (hf : DifferentiableOn ℂ f {w : ℂ | l < w.re}) {c : ℂ} (hc : l < c.re) :
    ∀ w : ℂ, l < w.re → HasDerivAt (fun z => wedgeIntegral c z f) (f w) w := by
  intro w hw
  let r := max c.re w.re+1
  let b := min c.im w.im-1
  let u := max c.im w.im+1
  have bound (y : ℂ) (hl : l < y.re) (hr : y.re ≤ max c.re w.re)
      (hb : min c.im w.im ≤ y.im) (hu : y.im ≤ max c.im w.im) : y ∈ complexOpenRect l r b u :=
    ⟨⟨hl,by dsimp [r]; linarith⟩,⟨by dsimp [b]; linarith,by dsimp [u]; linarith⟩⟩
  exact holomorphic_rectangle_has_primitive (hf.mono (fun _ h => h.1.1))
    (bound c hc (le_max_left ..) (min_le_left ..) (le_max_left ..)) w
    (bound w hw (le_max_right ..) (min_le_right ..) (le_max_right ..))

/-- A single vanishing boundary period suffices for a single-valued
holomorphic primitive throughout the exterior of a disk. -/
theorem exterior_primitive_of_zero_angular_period {f : ℂ → ℂ} {R r : ℝ} (hR : 0 < R) (hr : R < r)
    (hf : ∀ z : ℂ, R < ‖z‖ → DifferentiableAt ℂ f z) (hzero : exteriorAngularPeriod f r = 0) :
    ∃ P : ℂ → ℂ, ∀ z : ℂ, R < ‖z‖ → HasDerivAt P (f z) z := by
  let l := Real.log R
  let c : ℂ := Real.log r
  let τ : ℂ := 2*Real.pi*I
  let U := {w : ℂ | l < w.re}
  let q := fun w : ℂ => exp w*f (exp w)
  let A := fun w => wedgeIntegral c w q
  have hc : c ∈ U := Real.log_lt_log hR hr
  have hop : IsOpen U := isOpen_Ioi.preimage continuous_re
  have hconn : IsPreconnected U := ((convex_Ioi l).linear_preimage reCLM.toLinearMap).isPreconnected
  have hrpos := hR.trans hr
  have hq (w) (hw : w ∈ U) : DifferentiableAt ℂ q w := by
    have hnorm : R < ‖exp w‖ := by rw [norm_exp,← Real.exp_log hR]; exact Real.exp_lt_exp.mpr hw
    exact (differentiableAt_exp).mul ((hf _ hnorm).comp w differentiableAt_exp)
  have hd (w) (hw : w ∈ U) : HasDerivAt A (q w) w :=
    right_half_plane_primitive (fun v hv => (hq v hv).differentiableWithinAt) hc w hw
  have reτ : τ.re = 0 := by simp [τ,mul_re]
  have mem (w) : w+τ ∈ U ↔ w ∈ U := by simp [U,reτ]
  have qper (w : ℂ) : q (w+τ) = q w := by
    change exp (w+2*Real.pi*I)*f (exp (w+2*Real.pi*I)) = _
    rw [exp_periodic]
  have base : A (c+τ)-A c = 0 := by
    have e (θ : ℝ) : exp ((Real.log r : ℝ)+(θ:ℂ)*I) = (r:ℂ)*exp ((θ:ℂ)*I) := by
      rw [exp_add,← ofReal_exp,Real.exp_log hrpos]
    simpa [A,wedgeIntegral,c,τ,q,Complex.mul_re,Complex.mul_im,e,smul_eq_mul,exteriorAngularPeriod] using hzero
  have increment (w) (hw : w ∈ U) : A (w+τ)-A w = 0 := by
    refine (primitives_difference_at_base hop hconn (F := fun w => A (w+τ)) (G := A)
      (fun v hv => ?_) hd hc w hw).trans base
    simpa only [qper,mul_one,Function.comp_def,id_eq] using (hd (v+τ) ((mem v).mpr hv)).comp v ((hasDerivAt_id v).add_const τ)
  let G := fun w : ℂ => if w ∈ U then A w else 0
  have periodic : Function.Periodic G τ := by
    intro w
    by_cases hw : w ∈ U
    · simpa [G,hw,(mem w).mpr hw] using sub_eq_zero.mp (increment w hw)
    · simp [G,mem,hw]
  have dg (w) (hw : w ∈ U) : HasDerivAt G (q w) w := by
    apply (hd w hw).congr_of_eventuallyEq
    filter_upwards [hop.mem_nhds hw] with z hz
    simp [G,hz]
  let P := fun z => G (log z)
  have lift (w : ℂ) : P (exp w) = G w := by
    obtain ⟨n,hn⟩ := exp_eq_exp_iff_exists_int.mp (exp_log (exp_ne_zero w))
    change G (log (exp w)) = G w
    rw [hn]
    exact periodic.int_mul n w
  refine ⟨P,?_⟩
  intro z hz
  have hn := norm_pos_iff.mp (hR.trans hz)
  have hw : log z ∈ U := by change Real.log R < (log z).re; rw [log_re]; exact Real.log_lt_log hR hz
  let J := fun v : ℂ => log (v/z)+log z
  have j0 : J z = log z := by simp [J,hn]
  have hj : HasDerivAt J z⁻¹ z := by
    have hsl : z/z ∈ slitPlane := by simp [hn]
    have d : HasDerivAt (fun v : ℂ => v/z) (1/z) z := (hasDerivAt_id z).div_const z
    have h := ((hasDerivAt_log hsl).comp (h := fun v : ℂ => v/z) z d).add_const (log z)
    simpa [J,hn,Function.comp_def] using h
  have eq : P =ᶠ[𝓝 z] G ∘ J := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds (show z ∈ ({0} : Set ℂ)ᶜ from hn)] with v hv
    change v ≠ 0 at hv
    have e : exp (J v) = v := by rw [show J v = log (v/z)+log z from rfl,exp_add,exp_log (div_ne_zero hv hn),exp_log hn,div_mul_cancel₀ _ hn]
    change P v = G (J v)
    exact (congrArg P e).symm.trans (lift (J v))
  have h := ((j0.symm ▸ dg (log z) hw).comp z hj).congr_of_eventuallyEq eq
  convert h using 1
  simp only [q,j0,exp_log hn]
  field_simp

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exterior_primitive_of_zero_angular_period
