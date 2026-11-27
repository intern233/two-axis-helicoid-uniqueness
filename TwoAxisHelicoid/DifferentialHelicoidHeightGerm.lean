import TwoAxisHelicoid.GeneralHelicoidLogCorrection
import TwoAxisHelicoid.SimplePoleInfinity

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology
open scoped Topology

/-- A residue-free order-two height differential and the holomorphic
logarithmic Gauss remainder already produce inverse height coordinates
and the normalized exponential correction. No height primitive or
exterior coordinate is supplied. -/
theorem differential_poles_give_true_helicoid_height_germ {h g P Q : ℂ → ℂ} {a : ℂ} (nz : a≠0)
    (pa : AnalyticAt ℂ P 0) (qa : AnalyticAt ℂ Q 0) {α : ℝ}
    (height : ∀ᶠ w in 𝓝[≠] (0:ℂ), h w=a/w^2+P w)
    (order : meromorphicOrderAt (logDeriv g) 0=(-2:ℤ))
    (gauss : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ g w ∧ g w≠0 ∧ logDeriv g w-I*(α:ℂ)*h w=Q w) :
    α≠0 ∧ ∃ H k F : ℂ → ℂ, AnalyticAt ℂ k 0 ∧ k 0=0 ∧ AnalyticAt ℂ F 0 ∧ F 0=0 ∧
      (∀ᶠ w in 𝓝[≠] (0:ℂ), HasDerivAt H (h w) w ∧ k (H w)⁻¹=w) ∧
      Tendsto (fun ξ : ℂ => k ξ⁻¹) (cobounded ℂ) (𝓝[≠] 0) ∧
      ∀ᶠ ξ in cobounded ℂ, H (k ξ⁻¹)=ξ ∧ g (k ξ⁻¹)=exp (I*(α:ℂ)*ξ+F ξ⁻¹) := by
  obtain ⟨r,rp,an⟩ := Metric.mem_nhds_iff.mp pa.eventually_analyticAt
  let J := fun z => wedgeIntegral 0 z P
  let B := ball (0:ℂ) r
  have pd : DifferentiableOn ℂ P B := fun z hz => (an hz).differentiableAt.differentiableWithinAt
  have dJ (w : ℂ) (hw : w∈B) : HasDerivAt J (P w) w :=
    pd.isConservativeOn.hasDerivAt_wedgeIntegral pd.continuousOn hw
  have aj : AnalyticAt ℂ J 0 := (show DifferentiableOn ℂ J B from fun z hz =>
    (dJ z hz).differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball 0 (mem_ball_self rp)
  let H := simplePoleCoordinate (-a) J
  have dh : ∀ᶠ w in 𝓝[≠] (0:ℂ), HasDerivAt H (h w) w := by
    filter_upwards [height,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) rp),self_mem_nhdsWithin] with w he hw ne
    change w≠0 at ne
    have pole : HasDerivAt (fun u : ℂ => -a/u) (a/w^2) w := by
      simpa using! (hasDerivAt_const w (-a)).div (hasDerivAt_id w) ne
    rw [he]
    exact pole.add (dJ w hw)
  obtain ⟨pitch,c,f,fa,f0,rep⟩ := general_end_normalized_exponential_of_log_difference order qa
    (gauss.and dh |>.mono fun _ t => ⟨t.1.1,t.1.2.1,t.2,t.1.2.2⟩)
  let Hc := simplePoleCoordinate (-a) (fun w => J w+c)
  have eq (w : ℂ) : Hc w=H w+c := by dsimp [Hc,H,simplePoleCoordinate]; abel
  obtain ⟨k,ka,k0,lim,right,left,_⟩ := simplePoleCoordinate_inverse_at_infinity (neg_ne_zero.mpr nz)
    (aj.add analyticAt_const : AnalyticAt ℂ (fun w => J w+c) 0)
  refine ⟨pitch,Hc,k,f ∘ k,ka,k0,?_,?_,?_,lim,?_⟩
  · exact (k0 ▸ fa).comp ka
  · simp only [Function.comp_apply,k0,f0]
  · filter_upwards [dh,left] with w dw lw
    exact ⟨(dw.add_const c).congr_of_eventuallyEq (Eventually.of_forall eq),lw⟩
  · filter_upwards [right,lim.eventually rep] with ξ hξ hg
    refine ⟨hξ,?_⟩
    have hx := (eq (k ξ⁻¹)).symm.trans hξ
    simpa only [hx,Function.comp_apply] using hg.2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.differential_poles_give_true_helicoid_height_germ
