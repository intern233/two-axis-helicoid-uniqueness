import TwoAxisHelicoid.AntiholomorphicChartGerms
import TwoAxisHelicoid.ComplexEndCompactification
import TwoAxisHelicoid.AlignedGaussLogGerm

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology ComplexConjugate

/-- A physical involution that is antiholomorphic in a puncture chart
extends at the added point as a regular antiholomorphic germ. Its
nonzero derivative follows from the actual equation for its square. -/
theorem antiholomorphic_involution_at_puncture {M : Type*} [TopologicalSpace M] [T2Space M]
    (E : PuncturedComplexEnd M) (f : M ≃ₜ M) (inv : Function.Involutive f)
    (anti : ∀ x∈E.coord.source, f x∈E.coord.source →
      AnalyticAt ℂ (E.coord ∘ f ∘ E.coord.symm ∘ conj) (conj (E.coord x))) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k 0 ∧ k 0=0 ∧ deriv k 0≠0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), k z∈E.coord.target ∧ E.coord.symm (k z)=f (E.coord.symm (conj z)) := by
  classical
  let c := E.coord
  let k := fun z : ℂ => if z=0 then 0 else c (f (c.symm (conj z)))
  have zero : k 0=0 := by simp [k]
  have tc := conjugation_tendsto_punctured_origin
  have source : c.source∈cocompact M := by simpa only [c,compl_compl] using E.compact_core.compl_mem_cocompact
  have target : c.target∈𝓝[≠] (0:ℂ) := by
    change E.coord.target∈_
    rw [E.target_eq]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ E.radius_pos)) self_mem_nhdsWithin
  have homeo : Tendsto f (cocompact M) (cocompact M) := f.map_cocompact.le
  have escape := homeo.comp (E.from_zero.comp tc)
  have germ : k =ᶠ[𝓝[≠] (0:ℂ)] c ∘ f ∘ c.symm ∘ conj := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp [k,show z≠0 from hz,Function.comp_def]
  have cont : ContinuousAt k 0 := by
    rw [continuousAt_iff_punctured_nhds,zero]
    exact (E.to_zero.comp escape).congr' germ.symm
  have data : ∀ᶠ z in 𝓝[≠] (0:ℂ), k z∈c.target ∧ c.symm (k z)=f (c.symm (conj z)) := by
    filter_upwards [germ,escape.eventually source] with z h inside
    rw [h]
    exact ⟨c.map_source inside,c.left_inv inside⟩
  have ak : AnalyticAt ℂ k 0 := by
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ cont
    filter_upwards [tc.eventually target,escape.eventually source,punctured_germ_eventually_local germ] with z hz hs eq
    have a := anti (c.symm (conj z)) (c.map_target hz) hs
    change AnalyticAt ℂ (c ∘ f ∘ c.symm ∘ conj) (conj (c (c.symm (conj z)))) at a
    rw [c.right_inv hz,starRingEnd_self_apply] at a
    exact a.differentiableAt.congr_of_eventuallyEq eq
  have tk : Tendsto k (𝓝[≠] (0:ℂ)) (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨by simpa only [zero] using cont.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}:Set ℂ)ᶜ)),data.mono (fun z h => by
      have hz := h.1
      change k z∈E.coord.target at hz
      rw [E.target_eq] at hz
      exact hz.2)⟩
  let g := conj ∘ k ∘ conj
  have ga : AnalyticAt ℂ g 0 := by simpa only [map_zero] using reflected_analytic_germ ak
  have gz : g 0=0 := by simp only [g,Function.comp_apply,map_zero,zero]
  have eq : (k ∘ g) =ᶠ[𝓝[≠] (0:ℂ)] id := by
    filter_upwards [(tc.comp (tk.comp tc)).eventually germ,tc.eventually data,target] with z he h hz
    change k (g z)=z
    rw [he]
    change c (f (c.symm (conj (conj (k (conj z))))))=z
    simp only [starRingEnd_self_apply] at h ⊢
    rw [h.2,inv,c.right_inv hz]
  have full : (k ∘ g) =ᶠ[𝓝 (0:ℂ)] id := by
    have rest : ∀ᶠ z in 𝓝 (0:ℂ), z≠0 → k (g z)=z := by
      change ∀ᶠ z in 𝓝[≠] (0:ℂ), k (g z)=z at eq
      simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using eq
    filter_upwards [rest] with z h
    by_cases zz : z=0
    · simp only [zz,Function.comp_apply,gz,zero,id_eq]
    · exact h zz
  have one := (deriv_comp 0 (show DifferentiableAt ℂ k (g 0) by rw [gz]; exact ak.differentiableAt) ga.differentiableAt).symm.trans
    (full.deriv_eq.trans (deriv_id 0))
  rw [gz] at one
  exact ⟨k,ak,zero,fun e => by simp [e] at one,data⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.antiholomorphic_involution_at_puncture
