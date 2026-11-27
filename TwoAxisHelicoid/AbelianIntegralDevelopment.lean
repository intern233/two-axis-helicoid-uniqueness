import TwoAxisHelicoid.NonvanishingTorusDifferential
import TwoAxisHelicoid.ChartLineIntegrals

namespace TwoAxisHelicoid.HolomorphicCoefficientDisks
open Complex Set Filter Function Topology
open scoped Topology unitInterval Manifold ContDiff
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- An abelian integral on a topological plane cover. The local
identity is meaningful at the zeros of the one-form as well. -/
def IsAbelianIntegral (A : HolomorphicCoefficientDisks M) (p : ℂ → M) (D : ℂ → ℂ) : Prop :=
  ∀ i z, p z∈A.primitives.domain i → ∀ᶠ w in 𝓝 z,
    D w-A.localIntegral i (chartAt ℂ i (p w))=D z-A.localIntegral i (chartAt ℂ i (p z))

theorem exists_abelian_integral [IsManifold 𝓘(ℂ,ℂ) ω M] (A : HolomorphicCoefficientDisks M) (compat : A.compatibleOneForm)
    (p : ℂ → M) (pc : Continuous p) : ∃ D : ℂ → ℂ, Continuous D ∧ A.IsAbelianIntegral p D := by
  let U := fun i => p ⁻¹' A.primitives.domain i
  let f := fun i w => A.localIntegral i (chartAt ℂ i (p w))
  obtain ⟨D,germ⟩ := simply_connected_glue_local_primitives (0:ℂ) U (fun i => (A.primitives.domain_isOpen i).preimage pc) p
    (fun w => A.primitives.mem_domain (p w)) f (fun i j w inside => pc.continuousAt.tendsto.eventually (A.primitive_overlap_germ compat inside))
  have h : A.IsAbelianIntegral p D := germ
  refine ⟨D,continuous_iff_continuousAt.mpr (fun z => ?_),h⟩
  let i := p z
  have inside := A.primitives.mem_domain i
  have c := ((A.localIntegral_analyticAt i inside.2).continuousAt.comp ((chartAt ℂ i).continuousAt inside.1)).comp (pc.continuousAt (x := z))
  apply (c.add (show ContinuousAt (fun _ : ℂ => D z-A.localIntegral i (chartAt ℂ i (p z))) z from continuousAt_const)).congr_of_eventuallyEq
  filter_upwards [h i z inside] with w hw
  exact (sub_eq_iff_eq_add.mp hw).trans (add_comm _ _)

/-- The difference of abelian integrals at the endpoints of a lift is
the actual coordinate line integral of the original piecewise path. -/
theorem integral_chain_lifts_increment {A : HolomorphicCoefficientDisks M} {p : ℂ → M} (cover : IsCoveringMap p)
    {D : ℂ → ℂ} (dev : A.IsAbelianIntegral p D) {x y : M} {s : ℂ} (c : A.IntegralChain x y s) :
    ∀ u : ℂ, p u=x → ∃ v : ℂ, p v=y ∧ D v-D u=s := by
  induction c with
  | refl x => exact fun u h => ⟨u,h,sub_self _⟩
  | step i x y hx hy =>
    intro u hu
    let γ := A.segmentPath i hx hy
    let α := cover.liftPath γ u (γ.source.trans hu.symm)
    have lifts (t : unitInterval) : p (α t)=γ t := congrFun (cover.liftPath_lifts γ u (γ.source.trans hu.symm)) t
    let f := fun t : unitInterval => D (α t)-A.localIntegral i (chartAt ℂ i (p (α t)))
    have lc : IsLocallyConstant f := by
      apply (IsLocallyConstant.iff_eventually_eq _).mpr
      intro t
      have z := A.chartSegment_mem i hx hy t.2
      have atT : p (α t)∈A.primitives.domain i := by
        rw [lifts]
        change (chartAt ℂ i).symm (chartSegment i x y t)∈A.primitives.domain i
        have zt := A.ball_target i z
        refine ⟨(chartAt ℂ i).map_target zt,?_⟩
        change (chartAt ℂ i) ((chartAt ℂ i).symm (chartSegment i x y t))∈Metric.ball (chartAt ℂ i i) (A.radius i)
        rw [(chartAt ℂ i).right_inv zt]
        exact z
      exact α.continuous.continuousAt.tendsto.eventually (dev i (α t) atT)
    have e := lc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ (1:unitInterval)) (mem_univ (0:unitInterval))
    have start : α 0=u := cover.liftPath_zero _ _ _
    have stop := (lifts 1).trans γ.target
    refine ⟨α 1,stop,?_⟩
    dsimp only [f] at e
    rw [start,hu,stop] at e
    rw [A.segmentIntegral_eq i hx hy]
    linear_combination e
  | trans a b ha hb =>
    intro u hu
    obtain ⟨v,hv,e⟩ := ha u hu
    obtain ⟨w,hw,f⟩ := hb v hv
    exact ⟨w,hw,by linear_combination e+f⟩

theorem abelian_integral_period_is_constant {A : HolomorphicCoefficientDisks M} {p : ℂ → M}
    {D : ℂ → ℂ} (dev : A.IsAbelianIntegral p D) {b : ℂ} (shift : ∀ z, p (z+b)=p z) :
    ∀ z, D (z+b)=D z+(D b-D 0) := by
  let delta := fun z => D (z+b)-D z
  have lc : IsLocallyConstant delta := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    have h := A.primitives.mem_domain (p z)
    have hb : p (z+b)∈A.primitives.domain (p z) := shift z ▸ h
    have near : Tendsto (fun x : ℂ => x+b) (𝓝 z) (𝓝 (z+b)) := (continuous_id.add continuous_const).continuousAt
    filter_upwards [near.eventually (dev (p z) (z+b) hb),dev (p z) z h] with w hw hz
    rw [shift,shift] at hw
    change D (w+b)-D w=D (z+b)-D z
    linear_combination hw-hz
  intro z
  have eq := lc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ z) (mem_univ 0)
  change D (z+b)-D z=D (0+b)-D 0 at eq
  rw [zero_add] at eq
  linear_combination eq

/-- Every displacement in the cover is realized by a finite path in
genuine surface charts. This also applies when the given topological
marking is merely continuous. -/
theorem abelian_increment_has_integral_chain {A : HolomorphicCoefficientDisks M} {p : ℂ → M} (pc : Continuous p)
    {D : ℂ → ℂ} (dev : A.IsAbelianIntegral p D) (u v : ℂ) :
    Nonempty (A.IntegralChain (p u) (p v) (D v-D u)) := by
  let R := fun a b : ℂ => Nonempty (A.IntegralChain (p a) (p b) (D b-D a))
  have join {a b c : ℂ} (ab : R a b) (bc : R b c) : R a c := by
    obtain ⟨f⟩ := ab
    obtain ⟨g⟩ := bc
    have z := IntegralChain.trans f g
    rw [show D b-D a+(D c-D b)=D c-D a by abel] at z
    exact ⟨z⟩
  have steps (a : ℂ) : ∀ᶠ b in 𝓝 a, R a b ∧ R b a := by
    let i := p a
    have h := A.primitives.mem_domain i
    filter_upwards [pc.continuousAt.eventually ((A.primitives.domain_isOpen i).mem_nhds h),dev i a h] with b hb e
    have f := IntegralChain.step (A := A) i (p a) (p b) h hb
    have g := IntegralChain.step (A := A) i (p b) (p a) hb h
    rw [A.segmentIntegral_eq i h hb,show A.localIntegral i (chartAt ℂ i (p b))-A.localIntegral i (chartAt ℂ i (p a))=D b-D a by linear_combination -e] at f
    rw [A.segmentIntegral_eq i hb h,show A.localIntegral i (chartAt ℂ i (p a))-A.localIntegral i (chartAt ℂ i (p b))=D a-D b by linear_combination e] at g
    exact ⟨⟨f⟩,⟨g⟩⟩
  let S := {b : ℂ | R u b}
  have so : IsOpen S := isOpen_iff_mem_nhds.mpr (fun b hb => (steps b).mono (fun _ e => join hb e.1))
  have co : IsOpen Sᶜ := isOpen_iff_mem_nhds.mpr (fun b hb => (steps b).mono (fun _ e hy => hb (join hy e.2)))
  have su : u∈S := by
    change Nonempty (A.IntegralChain (p u) (p u) (D u-D u))
    rw [sub_self]
    exact ⟨.refl _⟩
  have sq := (show IsClopen S from ⟨isOpen_compl_iff.mp co,so⟩).eq_univ ⟨u,su⟩
  exact (show v∈S from sq ▸ mem_univ v)

end TwoAxisHelicoid.HolomorphicCoefficientDisks
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.exists_abelian_integral
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.integral_chain_lifts_increment
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.abelian_increment_has_integral_chain
