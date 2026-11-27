import TwoAxisHelicoid.RuledGraphSideContact
import TwoAxisHelicoid.ContactProjectionMinor
import TwoAxisHelicoid.HelicoidLocalCoincidence

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ContDiff

/-- The comparison helicoid has a planar drift equation up to an analytic
unit, even when the sheet touches its vertical axis. -/
theorem harmonic_immersion_helicoid_drift_factor {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (reg : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun u => X u j) w) ∧ ConformalCoordinateDerivatives X w)
    (inj : Function.Injective (fderiv ℝ X z)) {g : ℂ} (hg : normSq g=1) (α b : ℝ)
    : HasPlanarDriftFactorAt (fun w => axisHelicoidSide g α b (X w)) z := by
  let V := fun h : ℝ => g*Complex.exp (I*(α*(h-b):ℝ))
  let c := fun h => (V h).re
  let s := fun h => (V h).im
  have an (h : ℝ) : AnalyticAt ℝ V h := by
    have r : AnalyticAt ℝ (fun u : ℝ => α*(u-b)) h := analyticAt_const.mul (analyticAt_id.sub analyticAt_const)
    have e : AnalyticAt ℝ (fun u : ℝ => I*(α*(u-b):ℝ)) h := analyticAt_const.mul ((ofRealCLM.analyticAt _).comp r)
    exact analyticAt_const.mul ((analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp (show AnalyticAt ℝ (fun u : ℝ => I*(α*(u-b):ℝ)) h from e))
  have ac (h : ℝ) : AnalyticAt ℝ c h := (reCLM.analyticAt _).comp (an h)
  have as' (h : ℝ) : AnalyticAt ℝ s h := (imCLM.analyticAt _).comp (an h)
  have dV (h : ℝ) : HasDerivAt V (I*((α:ℂ)*V h)) h := by
    have hd : HasDerivAt (fun u : ℝ => α*(u-b)) α h := by simpa only [mul_one] using! ((hasDerivAt_id h).sub_const b).const_mul α
    have H := ((hd.ofReal_comp.const_mul I).cexp).const_mul g
    convert H using 1
    dsimp [V]
    ring
  have dc (h : ℝ) : HasDerivAt c (-α*s h) h := by
    have H := reCLM.hasFDerivAt.comp_hasDerivAt h (dV h)
    change HasDerivAt c (I*((α:ℂ)*V h)).re h at H
    simpa only [c,s,Complex.I_mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,neg_mul] using H
  have ds (h : ℝ) : HasDerivAt s (α*c h) h := by
    have H := imCLM.hasFDerivAt.comp_hasDerivAt h (dV h)
    change HasDerivAt s (I*((α:ℂ)*V h)).im h at H
    simpa only [c,s,Complex.I_mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using H
  have ax : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (reg.self_of_nhds.1 j)
  have reduce (σ : Equiv.Perm (Fin 3)) (C S : ℝ → ℝ) (k : ℝ)
      (aC : ∀ h, AnalyticAt ℝ C h) (aS : ∀ h, AnalyticAt ℝ S h)
      (dC : ∀ h, HasDerivAt C (-k*S h) h) (dS : ∀ h, HasDerivAt S (k*C h) h)
      (n : C (X z (σ 1)) ≠ 0)
      (eq : ∀ v : Fin 3 → ℝ, ruledGraphSide C S (fun i => v (σ i))=axisHelicoidSide g α b v) :
      HasPlanarDriftFactorAt (fun w => axisHelicoidSide g α b (X w)) z := by
    let T : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (σ j))
    let Y := T ∘ X
    have it : Function.Injective T := by
      intro p q e
      funext j
      obtain ⟨l,rfl⟩ := σ.surjective j
      exact congrFun e l
    have ii : Function.Injective (fderiv ℝ Y z) := by
      rw [(T.hasFDerivAt.comp z ax.differentiableAt.hasFDerivAt).fderiv]; exact it.comp inj
    have rr : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun u => Y u j) w) ∧ ConformalCoordinateDerivatives Y w :=
      reg.mono fun w h => ⟨fun j => h.1 (σ j),conformal_reindex_coordinates σ h.2⟩
    have hh (w : ℂ) : ruledGraphSide C S (Y w)=axisHelicoidSide g α b (X w) := eq _
    rw [show (fun w => axisHelicoidSide g α b (X w))=(fun w => ruledGraphSide C S (Y w)) from (funext hh).symm]
    exact harmonic_chart_ruled_drift_factor rr ii C S k aC aS dC dS n
  by_cases hc : c (X z 2)=0
  · have ns : s (X z 2) ≠ 0 := by
      intro h
      have v0 : V (X z 2)=0 := Complex.ext hc h
      have gn : g ≠ 0 := fun e => by simp [e] at hg
      exact mul_ne_zero gn (Complex.exp_ne_zero _) v0
    obtain ⟨σ,e₀,e₁,e₂⟩ : ∃ σ : Equiv.Perm (Fin 3), σ 0=0 ∧ σ 1=2 ∧ σ 2=1 := by decide
    apply reduce σ s c (-α) as' ac (fun h => by simpa only [neg_neg] using ds h) dc (e₁.symm ▸ ns)
    intro p
    change s (p (σ 1))*p (σ 2)+c (p (σ 1))*p (σ 0)=c (p 2)*p 0+s (p 2)*p 1
    rw [e₀,e₁,e₂,add_comm]
  · obtain ⟨σ,e₀,e₁,e₂⟩ : ∃ σ : Equiv.Perm (Fin 3), σ 0=1 ∧ σ 1=2 ∧ σ 2=0 := by decide
    apply reduce σ c s α ac as' dc ds (e₁.symm ▸ hc)
    intro p
    change c (p (σ 1))*p (σ 2)+s (p (σ 1))*p (σ 0)=c (p 2)*p 0+s (p 2)*p 1
    rw [e₀,e₁,e₂]

/-- Interior one-sided contact with a ruled comparison helicoid forces
local coincidence, including at its vertical axis. The chosen Cartesian
graph direction may depend on the contact height. -/
theorem harmonic_immersion_one_sided_helicoid {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (reg : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun u => X u j) w) ∧ ConformalCoordinateDerivatives X w)
    (inj : Function.Injective (fderiv ℝ X z)) {g : ℂ} (hg : normSq g=1) (α b : ℝ)
    (on : X z ∈ range (axisRuledHelicoid g α b))
    (side : (∀ᶠ w in 𝓝 z, 0 ≤ axisHelicoidSide g α b (X w)) ∨ (∀ᶠ w in 𝓝 z, axisHelicoidSide g α b (X w) ≤ 0)) :
    ∀ᶠ w in 𝓝 z, X w ∈ range (axisRuledHelicoid g α b) := by
  have drift := harmonic_immersion_helicoid_drift_factor reg inj hg α b
  have zero := (axisHelicoidSide_eq_zero_iff hg α b _).mpr on
  exact (drift.interior_contact zero side).mono fun w hw => (axisHelicoidSide_eq_zero_iff hg α b _).mp hw

/-- The signed side of a comparison helicoid takes both strict signs in
every neighborhood of each point of intersection with the embedded
punctured torus. This includes tangential intersections. -/
theorem marked_torus_crosses_comparison_helicoid {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) (hE : IsClosedEmbedding (harmonicTorusImmersion hX))
    {g : ℂ} (hg : normSq g=1) (α b : ℝ) {z : ℂ} (hz : z ∉ L.lattice) (on : X z ∈ range (axisRuledHelicoid g α b)) :
    (∃ᶠ w in 𝓝 z, 0 < axisHelicoidSide g α b (X w)) ∧ (∃ᶠ w in 𝓝 z, axisHelicoidSide g α b (X w) < 0) := by
  have reg : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun u => X u j) w) ∧ ConformalCoordinateDerivatives X w :=
    Filter.mem_of_superset (L.isClosed_lattice.isOpen_compl.mem_nhds hz) fun w hw => ⟨hX.harmonic w hw,hX.conformal w hw⟩
  have no := marked_torus_not_locally_contained_in_helicoid hX hE hg α b hz
  constructor
  · intro h
    exact no (harmonic_immersion_one_sided_helicoid reg (hX.immersion z hz) hg α b on (.inr (h.mono fun _ hw => le_of_not_gt hw)))
  · intro h
    exact no (harmonic_immersion_one_sided_helicoid reg (hX.immersion z hz) hg α b on (.inl (h.mono fun _ hw => le_of_not_gt hw)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_immersion_helicoid_drift_factor
#print axioms TwoAxisHelicoid.harmonic_immersion_one_sided_helicoid
#print axioms TwoAxisHelicoid.marked_torus_crosses_comparison_helicoid
