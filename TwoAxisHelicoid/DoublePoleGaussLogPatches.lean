import TwoAxisHelicoid.GaussLogHalfPlanePatches
import TwoAxisHelicoid.GaussMultiplierRigidity
import TwoAxisHelicoid.StripPrimitives
import TwoAxisHelicoid.TorusDoublePoleResidue
import Mathlib.Analysis.Calculus.LogDeriv

namespace TwoAxisHelicoid
open Complex Set Metric Filter Bornology
open scoped Topology

theorem analytic_log_right_half_plane {g : ℂ → ℂ} {B : ℝ}
    (ha : ∀ z : ℂ, B<z.re → AnalyticAt ℂ g z) (hn : ∀ z : ℂ, B<z.re → g z≠0) :
    ∃ W : ℂ → ℂ, ∀ z : ℂ, B<z.re → AnalyticAt ℂ W z ∧ exp (W z)=g z ∧ deriv W z=logDeriv g z := by
  let U := {z : ℂ | B<z.re}
  let b : ℂ := (B+1:ℝ)
  let F := fun z => wedgeIntegral b z (logDeriv g)
  have ob : b∈U := by change B<B+1; linarith
  have op : IsOpen U := isOpen_lt continuous_const continuous_re
  have hF (z : ℂ) (hz : z∈U) : HasDerivAt F (logDeriv g z) z := by
    let a := max b.re z.re+1
    let l := min b.im z.im-1
    let u := max b.im z.im+1
    have bg : B<b.re := ob
    have zg : B<z.re := hz
    have bd : b∈complexOpenRect B a l u := ⟨⟨bg,by dsimp [a]; linarith [le_max_left b.re z.re]⟩,
      ⟨by dsimp [l]; linarith [min_le_left b.im z.im],by dsimp [u]; linarith [le_max_left b.im z.im]⟩⟩
    have zd : z∈complexOpenRect B a l u := ⟨⟨zg,by dsimp [a]; linarith [le_max_right b.re z.re]⟩,
      ⟨by dsimp [l]; linarith [min_le_right b.im z.im],by dsimp [u]; linarith [le_max_right b.im z.im]⟩⟩
    apply holomorphic_rectangle_has_primitive (c := b) _ bd z zd
    intro v hv
    exact ((ha v hv.1.1).deriv.div (ha v hv.1.1) (hn v hv.1.1)).differentiableAt.differentiableWithinAt
  have af := (show DifferentiableOn ℂ F U from fun z hz => (hF z hz).differentiableAt.differentiableWithinAt).analyticOnNhd op
  have c0 : IsConnected U := (convex_halfSpace_re_gt B).isConnected ⟨b,ob⟩
  obtain ⟨k,hk,eq⟩ := equal_logarithmic_derivatives_constant_ratio op c0
    (f := fun z => exp (F z)) (g := g) (fun z hz => (hF z hz).cexp.differentiableAt)
    (fun z hz => (ha z hz).differentiableAt) (fun z _ => exp_ne_zero _) hn (by
      intro z hz
      rw [(hF z hz).cexp.deriv,mul_div_cancel_left₀ _ (exp_ne_zero _)]
      rfl)
  refine ⟨fun z => k.log+F z,fun z hz => ⟨analyticAt_const.add (af z hz),?_,?_⟩⟩
  · rw [exp_add,exp_log hk,← eq z hz]
  · exact ((hF z hz).const_add _).deriv

/-- A double pole of the genuine logarithmic Gauss derivative supplies
a scaled inverse parameter and a holomorphic logarithm on a right
half-plane. The possible residue, and the value assigned at the
puncture, are unrestricted. -/
theorem double_pole_gauss_log_right_half_plane {G : ℂ → ℂ} (hm : MeromorphicAt (logDeriv G) 0)
    (pole : meromorphicOrderAt (logDeriv G) 0= -2) :
    ∃ (a : ℂ) (B : ℝ) (W : ℂ → ℂ), a≠0 ∧ 0<B ∧
      (∀ z : ℂ, B<z.re → AnalyticAt ℂ W z ∧ exp (W z)=G (a/z)) ∧
      ∀ δ : ℝ, 0<δ → ∃ A : ℝ, ∀ z : ℂ, A<z.re → AnalyticAt ℂ W z ∧ ‖deriv W z-I‖≤δ := by
  obtain ⟨u,hu,hu0,fac⟩ := (meromorphicOrderAt_eq_int_iff hm).mp pole
  let a := I*u 0
  have ha : a≠0 := mul_ne_zero I_ne_zero hu0
  let v := fun z : ℂ => a/z
  have vlim : Tendsto v (cobounded ℂ) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · simpa [v,div_eq_mul_inv] using (tendsto_const_nhds (x := a)).mul (tendsto_inv₀_cobounded (α := ℂ))
    · filter_upwards [eventually_cobounded_le_norm (E := ℂ) (1:ℝ)] with z hz
      exact div_ne_zero ha (fun e => by rw [e,norm_zero] at hz; linarith)
  let g := G ∘ v
  have data : ∀ᶠ z in cobounded ℂ, DifferentiableAt ℂ g z ∧ g z≠0 ∧ logDeriv g z= -u (v z)/a := by
    filter_upwards [vlim.eventually fac,vlim.eventually ((hu.continuousAt.eventually_ne hu0).filter_mono nhdsWithin_le_nhds),
      eventually_cobounded_le_norm (E := ℂ) (1:ℝ)] with z hfac nu bound
    have nz : z≠0 := fun e => by rw [e,norm_zero] at bound; linarith
    have nv : v z≠0 := div_ne_zero ha nz
    have eq : logDeriv G (v z)=u (v z)/(v z)^2 := by
      simpa [sub_zero,smul_eq_mul,zpow_neg,div_eq_mul_inv,mul_comm] using hfac
    have ne : logDeriv G (v z)≠0 := eq ▸ div_ne_zero nu (pow_ne_zero _ nv)
    have dg : DifferentiableAt ℂ G (v z) := by
      by_contra h
      exact ne (by simp [logDeriv_apply,deriv_zero_of_not_differentiableAt h])
    have ng : G (v z)≠0 := fun e => ne (by simp [logDeriv_apply,e])
    have vd : HasDerivAt v (-a/z^2) z := by
      simpa only [zero_mul,one_mul,mul_one,zero_sub,id_eq] using! (hasDerivAt_const z a).div (hasDerivAt_id z) nz
    refine ⟨dg.comp z vd.differentiableAt,ng,?_⟩
    rw [logDeriv_comp dg vd.differentiableAt,vd.deriv,eq]
    dsimp [v]
    field_simp [ha,nz]
  obtain ⟨T,_,hT⟩ := hasBasis_cobounded_norm.eventually_iff.mp data
  let B := max 1 T
  have item z (hz : B<z.re) := hT ((le_max_right 1 T).trans (hz.le.trans (re_le_norm z)))
  have op : IsOpen {z : ℂ | B<z.re} := isOpen_lt continuous_const continuous_re
  have analytic := (show DifferentiableOn ℂ g {z : ℂ | B<z.re} from fun z hz => (item z hz).1.differentiableWithinAt).analyticOnNhd op
  obtain ⟨W,hW⟩ := analytic_log_right_half_plane analytic (fun z hz => (item z hz).2.1)
  have val : -u 0/a=I := by dsimp [a]; field_simp [hu0,I_ne_zero]; simp
  have limit : Tendsto (fun z => -u (v z)/a) (cobounded ℂ) (𝓝 I) := val ▸
    ((hu.continuousAt.tendsto.comp (vlim.mono_right nhdsWithin_le_nhds)).neg.div_const a)
  refine ⟨a,B,W,ha,lt_of_lt_of_le zero_lt_one (le_max_left _ _),fun z hz => ⟨(hW z hz).1,(hW z hz).2.1⟩,?_⟩
  intro δ hd
  obtain ⟨D,_,hD⟩ := hasBasis_cobounded_norm.eventually_iff.mp ((Metric.tendsto_nhds.mp limit) δ hd)
  refine ⟨max B D,fun z hz => ?_⟩
  have bz := (le_max_left B D).trans_lt hz
  refine ⟨(hW z bz).1,?_⟩
  rw [(hW z bz).2.2,(item z bz).2.2]
  simpa only [dist_eq_norm] using (hD ((le_max_right B D).trans (hz.le.trans (re_le_norm z)))).le

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.double_pole_gauss_log_right_half_plane
