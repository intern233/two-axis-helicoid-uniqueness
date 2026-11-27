import TwoAxisHelicoid.HarmonicAxisReflection

namespace TwoAxisHelicoid
open Complex Set Metric Filter InnerProductSpace
open scoped Topology ComplexConjugate

theorem harmonic_axis_germ_reflects {Y : ℂ → Fin 3 → ℝ}
    (hh : ∀ j, HarmonicAt (fun z => Y z j) 0)
    (hx : ∀ᶠ z in 𝓝 (0:ℂ), Y z 0 = z.re)
    (hr : ∀ᶠ (s : ℝ) in 𝓝 0, Y (s:ℂ) = ![s,0,0]) :
    ∀ᶠ z in 𝓝 (0:ℂ), Y (conj z) = halfTurnX (Y z) := by
  have ha : ∀ᶠ z in 𝓝 (0:ℂ), ∀ j, HarmonicAt (fun w => Y w j) z := by
    rw [Filter.eventually_all]
    exact fun j => (isOpen_setOfPred_harmonicAt (f := fun w => Y w j)).mem_nhds (hh j)
  have hre : ∀ᶠ z in 𝓝 (0:ℂ), Y (z.re:ℂ) = ![z.re,0,0] :=
    (show Tendsto Complex.re (𝓝 (0:ℂ)) (𝓝 (0:ℝ)) from continuous_re.continuousAt).eventually hr
  obtain ⟨r,hr',hsub⟩ := Metric.mem_nhds_iff.mp (ha.and (hx.and hre))
  filter_upwards [ball_mem_nhds (0:ℂ) hr'] with z hz
  apply harmonic_axis_chart_reflects hr' (fun j w hw => (hsub hw).1 j)
    (fun w hw => (hsub hw).2.1) _ z hz
  intro x h
  simpa using (hsub h).2.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_axis_germ_reflects
