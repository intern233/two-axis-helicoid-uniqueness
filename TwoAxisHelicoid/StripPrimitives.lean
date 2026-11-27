import TwoAxisHelicoid.RectanglePrimitive
import Mathlib.Analysis.Convex.Topology

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Topology Interval

def complexHorizontalStrip (b u : ℝ) : Set ℂ := {z | z.im ∈ Ioo b u}

theorem complexHorizontalStrip_isOpen (b u : ℝ) : IsOpen (complexHorizontalStrip b u) :=
  isOpen_Ioo.preimage continuous_im

theorem complexHorizontalStrip_convex (b u : ℝ) : Convex ℝ (complexHorizontalStrip b u) :=
  (convex_Ioo b u).linear_preimage Complex.imCLM.toLinearMap

theorem complexOpenRect_convex (l r b u : ℝ) : Convex ℝ (complexOpenRect l r b u) :=
  ((convex_Ioo l r).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioo b u).linear_preimage Complex.imCLM.toLinearMap)

/-- The actual wedge integral gives a holomorphic primitive on an unbounded
horizontal strip. A bounded rectangle containing the base and the point
reduces the assertion to the proved rectangle theorem. -/
theorem holomorphic_horizontal_strip_has_primitive {f : ℂ → ℂ} {b u : ℝ}
    (hf : DifferentiableOn ℂ f (complexHorizontalStrip b u))
    {c : ℂ} (hc : c ∈ complexHorizontalStrip b u) :
    ∀ z ∈ complexHorizontalStrip b u,
      HasDerivAt (fun w => wedgeIntegral c w f) (f z) z := by
  intro z hz
  let l := min c.re z.re-1
  let r := max c.re z.re+1
  have hsub : complexOpenRect l r b u ⊆ complexHorizontalStrip b u := fun _ h => h.2
  have hc' : c ∈ complexOpenRect l r b u := by
    refine ⟨⟨?_,?_⟩,hc⟩
    · dsimp [l]; linarith [min_le_left c.re z.re]
    · dsimp [r]; linarith [le_max_left c.re z.re]
  have hz' : z ∈ complexOpenRect l r b u := by
    refine ⟨⟨?_,?_⟩,hz⟩
    · dsimp [l]; linarith [min_le_right c.re z.re]
    · dsimp [r]; linarith [le_max_right c.re z.re]
  exact holomorphic_rectangle_has_primitive (hf.mono hsub) hc' z hz'

/-- Equal actual derivatives give a constant difference on any connected
open domain. The value at a chosen point fixes that constant. -/
theorem primitives_difference_at_base {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {F G f : ℂ → ℂ} (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (hG : ∀ z ∈ U, HasDerivAt G (f z) z) {b : ℂ} (hb : b ∈ U) :
    ∀ z ∈ U, F z-G z = F b-G b := by
  obtain ⟨C,hC⟩ := hU.exists_is_const_of_deriv_eq_zero hc
    (f := fun z => F z-G z)
    (fun z hz => ((hF z hz).sub (hG z hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => by
      change deriv (F-G) z = 0
      simpa only [sub_self] using ((hF z hz).sub (hG z hz)).deriv)
  intro z hz
  exact (hC z hz).trans (hC b hb).symm

theorem primitive_path_integral_eq_sub {F f : ℂ → ℂ} {γ : ℝ → ℂ} {v : ℂ} {a b : ℝ}
    (hγ : ∀ s ∈ uIcc a b, HasDerivAt γ v s)
    (hF : ∀ s ∈ uIcc a b, HasDerivAt F (f (γ s)) (γ s))
    (hf : IntervalIntegrable (fun s => f (γ s)) volume a b) :
    v*(∫ s in a..b, f (γ s)) = F (γ b)-F (γ a) := by
  have hd (s : ℝ) (hs : s ∈ uIcc a b) :
      HasDerivAt (fun s => F (γ s)) (v*f (γ s)) s := by
    simpa only [Function.comp_def,mul_comm] using (hF s hs).comp s (hγ s hs)
  simpa only [intervalIntegral.integral_const_mul] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hf.const_mul v)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.holomorphic_horizontal_strip_has_primitive
