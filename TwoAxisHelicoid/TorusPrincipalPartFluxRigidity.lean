import TwoAxisHelicoid.PeriodicGaussLogConstant
import TwoAxisHelicoid.PeriodicMeromorphicDifferences
import TwoAxisHelicoid.TorusGaussFluxRigidity
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- Common finite negative Laurent coefficients in the actual lifted torus
coordinate. Each function may have a different analytic regular part. -/
def CommonLaurentPartAt (f g : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ (n : ℕ) (a : ℕ → ℂ) (s t : ℂ → ℂ), AnalyticAt ℂ s z ∧ AnalyticAt ℂ t z ∧
    (f =ᶠ[𝓝[≠] z] fun w => finitePrincipalPart n a z w+s w) ∧
    (g =ᶠ[𝓝[≠] z] fun w => finitePrincipalPart n a z w+t w)

theorem CommonLaurentPartAt.removable_difference {f g : ℂ → ℂ} {z : ℂ}
    (h : CommonLaurentPartAt f g z) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k z ∧ (fun w => g w-f w) =ᶠ[𝓝[≠] z] k := by
  obtain ⟨n,a,s,t,hs,ht,hf,hg⟩ := h
  exact removable_from_common_laurent_principal_part a hs ht hf hg

theorem periodic_removable_germ_at_translates (L : PeriodPair) {f : ℂ → ℂ}
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z)
    (hr : ∃ k : ℂ → ℂ, AnalyticAt ℂ k 0 ∧ f =ᶠ[𝓝[≠] 0] k) :
    ∀ ω ∈ L.lattice, ∃ k : ℂ → ℂ, AnalyticAt ℂ k ω ∧ f =ᶠ[𝓝[≠] ω] k := by
  obtain ⟨k,hk,he⟩ := hr
  intro ω hω
  have hshift : Tendsto (fun z : ℂ => z-ω) (𝓝[≠] ω) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,(show ∀ᶠ w in 𝓝[≠] ω, w ≠ ω from self_mem_nhdsWithin).mono fun _ hw e => hw (sub_eq_zero.mp e)⟩
    have hcont : Continuous (fun u : ℂ => u-ω) := continuous_id.sub continuous_const
    simpa using (hcont.continuousAt (x := ω)).tendsto.mono_left (nhdsWithin_le_nhds (s := ({ω}ᶜ : Set ℂ)))
  have hka : AnalyticAt ℂ k (ω-ω) := by simpa using hk
  have a : AnalyticAt ℂ (fun z : ℂ => z-ω) ω := analyticAt_id.sub analyticAt_const
  refine ⟨fun z => k (z-ω),hka.comp (f := fun z : ℂ => z-ω) a,?_⟩
  filter_upwards [hshift.eventually he] with w hw
  have e := hp (w-ω) ω hω
  rw [sub_add_cancel] at e
  exact e.trans hw

noncomputable def immersionGaussLog (p : ℂ → Fin 3 → ℂ) (z : ℂ) : ℂ :=
  deriv (nullGauss ∘ p) z/nullGauss (p z)

theorem immersionGaussLog_analyticAt {p : ℂ → Fin 3 → ℂ} {z : ℂ}
    (hp : ∀ j, AnalyticAt ℂ (fun w => p w j) z) (hpn : ComplexNull (p z))
    (hn : p z 2 ≠ 0) : AnalyticAt ℂ (immersionGaussLog p) z := by
  have hg : AnalyticAt ℂ (nullGauss ∘ p) z := nullGauss_analyticAt_of_height hp hpn hn
  exact hg.deriv.div hg (nullGauss_ne_zero_of_height hpn hn)

theorem immersionGaussLog_periodic (L : PeriodPair) {p : ℂ → Fin 3 → ℂ}
    (hp : ∀ z ω, ω ∈ L.lattice → p (z+ω) = p z) (z ω : ℂ) (hω : ω ∈ L.lattice) :
    immersionGaussLog p (z+ω) = immersionGaussLog p z := by
  let g := nullGauss ∘ p
  have hg : (fun w => g (w+ω)) = g := funext fun w => congrArg nullGauss (hp w ω hω)
  have hd := deriv_comp_add_const g ω z
  rw [hg] at hd
  unfold immersionGaussLog
  rw [hp z ω hω]
  exact congrArg (· / nullGauss (p z)) hd.symm

/-- Equal Laurent data on an arbitrary marked torus and a real spatial
horizontal flux witness imply a single rigid motion on its full punctured
surface, including the ordinary Gauss zero/pole representatives. -/
theorem marked_torus_common_laurent_parts_rigid_motion (L : PeriodPair)
    (X Y : PeriodTorus L → Fin 3 → ℝ) (p q : ℂ → Fin 3 → ℂ)
    (hp : ∀ z ∉ L.lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    (hq : ∀ z ∉ L.lattice, ∀ j, AnalyticAt ℂ (fun w => q w j) z)
    (hpn : ∀ z ∉ L.lattice, ComplexNull (p z)) (hqn : ∀ z ∉ L.lattice, ComplexNull (q z))
    (hpper : ∀ z ω, ω ∈ L.lattice → p (z+ω) = p z) (hqper : ∀ z ω, ω ∈ L.lattice → q (z+ω) = q z)
    (hX : ∀ z ∉ L.lattice, HasFDerivAt (X ∘ periodTorusProjection L) (nullRealDerivative (p z)) z)
    (hY : ∀ z ∉ L.lattice, HasFDerivAt (Y ∘ periodTorusProjection L) (nullRealDerivative (q z)) z)
    (hH : CommonLaurentPartAt (fun z => p z 2) (fun z => q z 2) 0)
    (hΩ : ∀ z, CommonLaurentPartAt (immersionGaussLog p) (immersionGaussLog q) z)
    {b : ℂ} (hb : b ∉ L.lattice) (hb' : p b 2 ≠ 0)
    {x y : ℂ} (γ : PiecewiseComplexPath (L.lattice : Set ℂ)ᶜ x y)
    (hγ : periodTorusProjection L x = periodTorusProjection L y)
    (hflux : (γ.integral (fun z => p z 0)).im ≠ 0 ∨ (γ.integral (fun z => p z 1)).im ≠ 0) :
    ∃ θ : ℝ, ∃ d : Fin 3 → ℝ, ∀ s : PuncturedPeriodTorus L,
      Y s.1 = verticalRotation (exp ((θ:ℂ)*I)) (X s.1)+d := by
  have hper (z ω : ℂ) (hω : ω ∈ L.lattice) : q (z+ω) 2 - p (z+ω) 2 = q z 2 - p z 2 := by
    rw [hqper _ _ hω,hpper _ _ hω]
  have hh := torus_height_difference_of_removable_germ L (fun z hz => hp z hz 2)
    (fun z hz => hq z hz 2) (X := fun s => X s 2) (Y := fun s => Y s 2)
    (fun z hz => (ContinuousLinearMap.proj 2 : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hX z hz))
    (fun z hz => (ContinuousLinearMap.proj 2 : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hY z hz))
    (fun z ω hω _ => hper z ω hω)
    (periodic_removable_germ_at_translates L hper hH.removable_difference)
  let Δ := fun z => immersionGaussLog q z-immersionGaussLog p z
  have hdper (z ω : ℂ) (hω : ω ∈ L.lattice) : Δ (z+ω) = Δ z := by
    simp only [Δ,immersionGaussLog_periodic L hpper _ _ hω,immersionGaussLog_periodic L hqper _ _ hω]
  obtain ⟨d,hd⟩ := elliptic_removable_germs_constant_germ L hdper (fun z => (hΩ z).removable_difference)
  have hdreg (z : ℂ) (hz : z ∉ L.lattice) (hn : p z 2 ≠ 0) : Δ z = d := by
    have hn' : q z 2 ≠ 0 := (hh _ hz).symm ▸ hn
    have ha : AnalyticAt ℂ Δ z := (immersionGaussLog_analyticAt (hq _ hz) (hqn _ hz) hn').sub
      (immersionGaussLog_analyticAt (hp _ hz) (hpn _ hz) hn)
    exact (removableGermExtension_eq ha.continuousAt Filter.EventuallyEq.rfl).symm.trans
      (removableGermExtension_eq continuousAt_const (hd z))
  have hd0 : d = 0 := by
    apply torus_gauss_log_constant_vanishes L hp hq hpn hqn
      (fun z ω hω _ => ⟨hpper z ω hω,hqper z ω hω⟩) hh hb hb'
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hb,
      (hp b hb 2).continuousAt.eventually_ne hb'] with z hz hn
    exact hdreg z hz hn
  apply punctured_torus_fixed_gauss_log_rigid_motion L X Y p q hp hq hpn hqn hX hY hh _ hb hb' γ hγ hflux
  exact fun z hz hn => sub_eq_zero.mp ((hdreg z hz hn).trans hd0)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_torus_common_laurent_parts_rigid_motion
