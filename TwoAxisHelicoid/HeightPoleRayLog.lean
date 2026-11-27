import TwoAxisHelicoid.MeromorphicRayOrder
import TwoAxisHelicoid.AxisLiftBound
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology

/-- The puncture variable has a continuous logarithm with bounded
imaginary part on any ray where the real part of a simple pole is
eventually positive. The residue may have arbitrary argument. -/
theorem bounded_puncture_log_on_height_ray {p : ℝ → ℂ} {H : ℂ → ℂ}
    (limit : Tendsto p atTop (𝓝[≠] 0)) (mer : MeromorphicAt H 0)
    (order : meromorphicOrderAt H 0=((-1:ℤ):WithTop ℤ))
    (ray : ∀ᶠ t in atTop, ContinuousAt p t ∧ ContinuousAt H (p t) ∧ 0<(H (p t)).re) :
    ∃ J : ℝ → ℂ, ∀ᶠ t in atTop, ContinuousAt J t ∧ exp (J t)=p t ∧ |(J t).im|≤3*Real.pi := by
  let f := (id : ℂ → ℂ)*H
  have fm : MeromorphicAt f 0 := analyticAt_id.meromorphicAt.mul mer
  have fo : meromorphicOrderAt f 0=0 := by
    rw [show meromorphicOrderAt f 0=_ from meromorphicOrderAt_mul analyticAt_id.meromorphicAt mer,meromorphicOrderAt_id,order]
    norm_num
  obtain ⟨b,nb,lim⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero fm fo
  let A := fun t => p t*H (p t)/b
  have near : Tendsto A atTop (𝓝 1) := by
    simpa only [div_self nb] using (show Tendsto A atTop (𝓝 (b/b)) from (lim.comp limit).div_const b)
  let J := fun t => log (A t)+log b-log (H (p t))
  refine ⟨J,?_⟩
  have apos : ∀ᶠ t in atTop, 0<(A t).re := (continuous_re.continuousAt.tendsto.comp near).eventually (lt_mem_nhds (by norm_num : (0:ℝ)<(1:ℂ).re))
  filter_upwards [ray,apos] with t h ap
  have hH : ContinuousAt (fun s => H (p s)) t := h.2.1.comp h.1
  have cA : ContinuousAt A t := (h.1.mul hH).div_const b
  have nA : A t≠0 := fun e => (by simpa only [e,Complex.zero_re] using ap : (0:ℝ)<0).false
  have nH : H (p t)≠0 := fun e => (by simpa only [e,Complex.zero_re] using h.2.2 : (0:ℝ)<0).false
  have argbound (z : ℂ) : |(log z).im|≤Real.pi := by rw [log_im,abs_le]; exact ⟨(neg_pi_lt_arg _).le,arg_le_pi _⟩
  have logH : ContinuousAt (fun s => log (H (p s))) t := ((continuousAt_clog (Or.inl h.2.2)).comp h.2.1).comp h.1
  refine ⟨(((continuousAt_clog (Or.inl ap)).comp cA).add continuousAt_const).sub logH,?_,?_⟩
  · dsimp only [J]
    rw [exp_sub,exp_add,exp_log nA,exp_log nb,exp_log nH]
    dsimp [A]
    field_simp
  · change |((log (A t)+log b-log (H (p t))):ℂ).im|≤_
    rw [Complex.sub_im,Complex.add_im,abs_le]
    obtain ⟨a₁,a₂⟩ := abs_le.mp (argbound (A t))
    obtain ⟨b₁,b₂⟩ := abs_le.mp (argbound b)
    obtain ⟨h₁,h₂⟩ := abs_le.mp (argbound (H (p t)))
    constructor <;> linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_puncture_log_on_height_ray
