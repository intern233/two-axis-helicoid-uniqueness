import TwoAxisHelicoid.ComplexVerticalSymmetry
import TwoAxisHelicoid.ComplexImplicitAnalytic
import TwoAxisHelicoid.VerticalSquareLimit

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate
attribute [local irreducible] complexThetaJet complexG complexGt thetaG verticalA

theorem exists_right_height_germ : ∃ ψ : ℂ → ℂ,
    AnalyticAt ℂ ψ 1 ∧ ψ 1 = (ellipticVerticalUpper:ℂ) ∧
    (∀ᶠ a : ℂ in 𝓝 1, ψ (2-a) = ψ a) ∧
    (∀ᶠ a : ℝ in 𝓝 1, (ψ a).im = 0) ∧
    (∀ᶠ t : ℝ in 𝓝[<] ellipticVerticalUpper, ψ (verticalA t) = (t:ℂ)) := by
  let T := ellipticVerticalUpper
  let p : ℂ × ℂ := (1,(T:ℂ))
  have htC : 0 < (T:ℂ).re := ellipticVerticalUpper_pos
  have hn : complexThetaJet T 0 (Real.pi*(1:ℂ)/2) ≠ 0 := by
    rw [complexThetaJet_ofReal]
    simpa only [Complex.ofReal_one] using theta_vertical_denominator ellipticVerticalUpper_pos
      (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)
  have heGt := (thetaG_real_t_hasDerivAt ellipticVerticalUpper_pos
    (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)).unique thetaG_one_t_hasDerivAt_upper
  have hGt : complexGt T 1 ≠ 0 := by
    have hh : (complexGt T 1).re = ellipticC T ellipticVerticalUpper_pos/(2*Real.pi) := by
      rw [← Complex.ofReal_one,complexGt_ofReal]
      exact heGt
    intro he
    rw [he,Complex.zero_re] at hh
    exact (div_pos (ellipticC_pos ellipticVerticalUpper_pos)
      (show 0 < 2*Real.pi by positivity)).ne' hh.symm
  have hswap : ContinuousAt (fun q : ℂ × ℂ => (q.2,q.1)) p := by fun_prop
  have hpos : ∀ᶠ q : ℂ × ℂ in 𝓝 p, 0 < q.2.re :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds htC
  have hdenC : ContinuousAt (fun q : ℂ × ℂ => complexThetaJet q.2 0 (Real.pi*q.1/2)) p :=
    (complexThetaJet_abscissa_continuousAt htC 0 (1:ℂ)).comp
      (f := fun q : ℂ × ℂ => (q.2,q.1)) (x := p) hswap
  have hden : ∀ᶠ q : ℂ × ℂ in 𝓝 p, complexThetaJet q.2 0 (Real.pi*q.1/2) ≠ 0 :=
    hdenC.eventually_ne hn
  have hD : ∀ᶠ q : ℂ × ℂ in 𝓝 p,
      HasStrictFDerivAt (fun q : ℂ × ℂ => complexG q.2 q.1) (complexGSwapDeriv q.1 q.2) q := by
    filter_upwards [hpos,hden] with q hq hnq
    exact complexG_swap_hasStrictFDerivAt hq hnq
  have hGtC : ContinuousAt (fun q : ℂ × ℂ => complexGt q.2 q.1) p :=
    (complexGt_joint_continuousAt htC hn).comp
      (f := fun q : ℂ × ℂ => (q.2,q.1)) (x := p) hswap
  have hInv : ∀ᶠ q : ℂ × ℂ in 𝓝 p,
      (complexGSwapDeriv q.1 q.2 ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    filter_upwards [hGtC.eventually_ne hGt] with q hq
    exact complexGSwapDeriv_inr_invertible hq
  let ψ := hD.self_of_nhds.implicitFunctionOfProdDomain hInv.self_of_nhds
  have hψ : AnalyticAt ℂ ψ 1 := complex_implicit_germ_analytic hD hInv
  have hrel := hD.self_of_nhds.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv.self_of_nhds
  have hψ1 : ψ 1 = (T:ℂ) := hrel.self_of_nhds.mp rfl
  have hbase : complexG T 1 = 0 := by
    simpa only [Complex.ofReal_one] using (complexG_ofReal T 1).trans thetaG_vertical_upper_one_zero
  have hgraph : Tendsto (fun a : ℂ => (a,ψ a)) (𝓝 1) (𝓝 p) := by
    simpa only [hψ1,p,id_eq] using (continuousAt_id.prodMk hψ.continuousAt).tendsto
  have hroot : ∀ᶠ a : ℂ in 𝓝 1, complexG (ψ a) a = 0 := by
    filter_upwards [hgraph.eventually hrel] with a ha
    exact (ha.mpr rfl).trans hbase
  have hreflect : Tendsto (fun a : ℂ => (2-a,ψ a)) (𝓝 1) (𝓝 p) := by
    have hc : ContinuousAt (fun a : ℂ => (2-a,ψ a)) 1 :=
      (continuousAt_const.sub continuousAt_id).prodMk hψ.continuousAt
    simpa only [hψ1,show (2-1:ℂ)=1 by norm_num,p] using hc.tendsto
  have heven : ∀ᶠ a : ℂ in 𝓝 1, ψ (2-a) = ψ a := by
    filter_upwards [hreflect.eventually hrel,hroot] with a ha hz
    apply ha.mp
    change complexG (ψ a) (2-a) = complexG T 1
    rw [complexG_reflect,hz,hbase]
  have hconj : Tendsto (fun a : ℂ => (conj a,conj (ψ a))) (𝓝 1) (𝓝 p) := by
    have hc : ContinuousAt (fun a : ℂ => (conj a,conj (ψ a))) 1 := by
      exact Complex.continuous_conj.continuousAt.prodMk
        (Complex.continuous_conj.continuousAt.comp hψ.continuousAt)
    simpa only [map_one,hψ1,Complex.conj_ofReal,p] using hc.tendsto
  have hreal : ∀ᶠ a : ℂ in 𝓝 1, ψ (conj a) = conj (ψ a) := by
    filter_upwards [hconj.eventually hrel,hroot] with a ha hz
    apply ha.mp
    change complexG (conj (ψ a)) (conj a) = complexG T 1
    rw [complexG_conj,hz,map_zero,hbase]
  have hrealR : ∀ᶠ a : ℝ in 𝓝 1, (ψ a).im = 0 := by
    have hcast : Tendsto (fun a : ℝ => (a:ℂ)) (𝓝 1) (𝓝 (1:ℂ)) := by
      simpa only [Complex.ofReal_one] using Complex.continuous_ofReal.continuousAt.tendsto (x := (1:ℝ))
    filter_upwards [hcast.eventually hreal] with a ha
    have hh := congrArg Complex.im ha
    simp only [Complex.conj_ofReal,Complex.conj_im] at hh
    linarith
  have hcurve : Tendsto (fun t : ℝ => ((verticalA t:ℂ),(t:ℂ))) (𝓝[<] T) (𝓝 p) := by
    have ha := Complex.continuous_ofReal.continuousAt.tendsto.comp verticalA_tendsto_one
    have ht : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[<] T) (𝓝 (T:ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_id'.mpr nhdsWithin_le_nhds)
    simpa only [Function.comp_def,Complex.ofReal_one,p] using ha.prodMk_nhds ht
  have hactual : ∀ᶠ t : ℝ in 𝓝[<] T, ψ (verticalA t) = (t:ℂ) := by
    filter_upwards [hcurve.eventually hrel,verticalDomain_eventually_left] with t ht hdom
    apply ht.mp
    change complexG t (verticalA t) = complexG T 1
    rw [complexG_ofReal,(verticalA_spec hdom).2,hbase]
  exact ⟨ψ,hψ,hψ1,heven,hrealR,hactual⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_right_height_germ
