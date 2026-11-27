import TwoAxisHelicoid.ComplexVerticalFunction
import TwoAxisHelicoid.ComplexImplicitAnalytic
import TwoAxisHelicoid.VerticalBranchDerivative
import Mathlib.Analysis.Analytic.Constructions

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaG thetaGa complexG complexGa complexThetaJet verticalA

theorem verticalA_complex_germ {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ (t:ℂ) ∧
      ∀ᶠ s : ℝ in 𝓝 t, ψ (s:ℂ) = (verticalA s:ℂ) := by
  have ha := (verticalA_spec ht).1
  let p : ℂ × ℂ := ((t:ℂ),(verticalA t:ℂ))
  have htC : 0 < (t:ℂ).re := ht.1
  have hden : complexThetaJet t 0 (Real.pi*(verticalA t:ℂ)/2) ≠ 0 := by
    rw [complexThetaJet_ofReal]
    exact theta_vertical_denominator ht.1 ha.1 (by linarith [ha.2])
  have hGa : complexGa t (verticalA t) ≠ 0 := by
    rw [complexGa_ofReal]
    intro he
    have hn := thetaGa_re_neg_unit ht.1 ha.1 ha.2
    rw [he,Complex.zero_re] at hn
    exact lt_irrefl _ hn
  have hpos : ∀ᶠ q : ℂ × ℂ in 𝓝 p, 0 < q.1.re :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds htC
  have hn : ∀ᶠ q : ℂ × ℂ in 𝓝 p, complexThetaJet q.1 0 (Real.pi*q.2/2) ≠ 0 :=
    (complexThetaJet_abscissa_continuousAt htC 0 (verticalA t:ℂ)).eventually_ne hden
  have hD : ∀ᶠ q : ℂ × ℂ in 𝓝 p,
      HasStrictFDerivAt (fun q : ℂ × ℂ => complexG q.1 q.2) (complexGDeriv q.1 q.2) q := by
    filter_upwards [hpos,hn] with q hq hnq
    exact complexG_joint_hasStrictFDerivAt hq hnq
  have hInv : ∀ᶠ q : ℂ × ℂ in 𝓝 p,
      (complexGDeriv q.1 q.2 ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    filter_upwards [(complexGa_joint_continuousAt htC hden).eventually_ne hGa] with q hq
    exact complexGDeriv_inr_invertible hq
  let ψ := hD.self_of_nhds.implicitFunctionOfProdDomain hInv.self_of_nhds
  have hψ : AnalyticAt ℂ ψ (t:ℂ) := complex_implicit_germ_analytic hD hInv
  have hrel := hD.self_of_nhds.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv.self_of_nhds
  have hcurve : ContinuousAt (fun s : ℝ => ((s:ℂ),(verticalA s:ℂ))) t :=
    Complex.continuous_ofReal.continuousAt.prodMk
      (Complex.continuous_ofReal.continuousAt.comp (verticalA_continuousAt ht))
  have hrel' := hcurve.eventually hrel
  have he : ∀ᶠ s : ℝ in 𝓝 t, ψ (s:ℂ) = (verticalA s:ℂ) := by
    filter_upwards [hrel',Ioo_mem_nhds ht.1 ht.2] with s hs hst
    apply hs.mp
    change complexG s (verticalA s) = complexG t (verticalA t)
    rw [complexG_ofReal,complexG_ofReal,(verticalA_spec hst).2,(verticalA_spec ht).2]
  exact ⟨ψ,hψ,he⟩

theorem verticalA_analyticAt {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    AnalyticAt ℝ verticalA t := by
  obtain ⟨ψ,hψ,he⟩ := verticalA_complex_germ ht
  have hr : AnalyticAt ℝ (fun s : ℝ => ψ (s:ℂ)) t :=
    (hψ.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  have hre : AnalyticAt ℝ (fun s : ℝ => (ψ (s:ℂ)).re) t :=
    (Complex.reCLM.analyticAt (ψ (t:ℂ))).comp (f := fun s : ℝ => ψ (s:ℂ)) hr
  apply hre.congr
  filter_upwards [he] with s hs
  simpa only [Complex.ofReal_re] using congrArg Complex.re hs

theorem verticalA_analyticOnNhd : AnalyticOnNhd ℝ verticalA (Ioo (0:ℝ) ellipticVerticalUpper) :=
  fun _ ht => verticalA_analyticAt ht

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.verticalA_analyticOnNhd
