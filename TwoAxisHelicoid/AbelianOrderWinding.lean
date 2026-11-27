import TwoAxisHelicoid.HolomorphicLocalWinding
import TwoAxisHelicoid.PlaneCoverChartOrientation
import TwoAxisHelicoid.AbelianIntegralFiniteFibers

namespace TwoAxisHelicoid.HolomorphicCoefficientDisks
open Complex Set Filter Topology Function
open scoped Topology ContDiff Manifold

/-- The local multiplicity of the abelian integral is positive, its
orientation sign is constant on the whole cover, and multiplicity one
forces the original differential to be nonzero at its base point. -/
theorem abelian_integral_local_multiplicities {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {A : HolomorphicCoefficientDisks M} {p : ℂ → M} (cover : IsCoveringMap p)
    {D : ℂ → ℂ} (dev : A.IsAbelianIntegral p D) (op : IsOpenMap D) :
    ∃ (s : ℤ) (k : ℂ → ℕ), (s=1 ∨ s= -1) ∧
      (∀ z, HasPlaneOrientationAt D z (((k z+1:ℕ):ℤ)*s)) ∧
      ∀ z, k z=0 → A.coefficient (p z) (chartAt ℂ (p z) (p z))≠0 := by
  obtain ⟨s,sign,orientation⟩ := complex_surface_plane_cover_orientation cover.isLocalHomeomorph
  have each (z : ℂ) : ∃ k : ℕ, HasPlaneOrientationAt D z (((k+1:ℕ):ℤ)*s) ∧
      (k=0 → A.coefficient (p z) (chartAt ℂ (p z) (p z))≠0) := by
    obtain ⟨l,hz,lift⟩ := cover.isLocalHomeomorph z
    let i := p z
    let a := chartAt ℂ i
    let e := l.trans a
    let f := fun w => A.localIntegral i w+(D z-A.localIntegral i (a i))
    have inc := A.primitives.mem_domain i
    have form : (e : ℂ → ℂ)=a ∘ p := by rw [lift]; rfl
    have center : e z=a i := congrFun form z
    have src : z∈e.source := ⟨hz,by change l z∈a.source; rw [← lift]; exact inc.1⟩
    have an : AnalyticAt ℂ f (e z) := by rw [center]; exact (A.localIntegral_analyticAt i inc.2).add analyticAt_const
    have der : HasDerivAt f (A.coefficient i (a i)) (e z) := by
      rw [center]
      exact (A.localIntegral_hasDerivAt i inc.2).add_const _
    have germ : D=ᶠ[𝓝 z] f ∘ e := by
      filter_upwards [dev i z inc] with w eq
      change D w=A.localIntegral i (e w)+(D z-A.localIntegral i (a i))
      rw [form]
      exact (sub_eq_iff_eq_add.mp eq).trans (add_comm _ _)
    let mult := analyticOrderAt (fun u => f u-f (e z)) (e z)
    have finite : mult≠⊤ := by
      intro h
      have zero := analyticOrderAt_eq_top.mp h
      have constant : ∀ᶠ w in 𝓝 z, D w=f (e z) := by
        filter_upwards [germ,(e.continuousAt src).eventually zero] with w hw eq
        exact hw.trans (sub_eq_zero.mp eq)
      obtain ⟨U,sub,uo,zu⟩ := mem_nhds_iff.mp constant
      have singleton : D '' U={f (e z)} := Subset.antisymm
        (image_subset_iff.mpr (fun _ hw => sub hw))
        (singleton_subset_iff.mpr ⟨z,zu,sub zu⟩)
      exact not_isOpen_singleton _ (singleton ▸ op U uo)
    obtain ⟨m,hm⟩ : ∃ m : ℕ, mult=(m:ℕ∞) := ⟨mult.toNat,(ENat.natCast_toNat_eq_self.mpr finite).symm⟩
    cases m with
    | zero =>
      have zero : mult=0 := hm
      exact (((an.sub analyticAt_const).analyticOrderAt_eq_zero.mp zero) (sub_self _)).elim
    | succ k =>
      have eo : HasPlaneOrientationAt e z s := form ▸ orientation z i inc.1
      have wnd := local_holomorphic_order_winding e src eo an hm
      refine ⟨k,wnd.congr germ,?_⟩
      intro vk
      subst k
      have ord : analyticOrderAt (deriv f) (e z)=0 := by
        have df := an.analyticOrderAt_deriv_add_one
        change analyticOrderAt (deriv f) (e z)+1=mult at df
        rw [hm] at df
        exact (ENat.add_left_injective_of_ne_top (by decide : (1:ℕ∞)≠⊤)) (by simpa using df)
      have non := an.deriv.analyticOrderAt_eq_zero.mp ord
      rwa [der.deriv] at non
  choose k wd simple using each
  exact ⟨s,k,sign,wd,simple⟩

end TwoAxisHelicoid.HolomorphicCoefficientDisks
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.abelian_integral_local_multiplicities
