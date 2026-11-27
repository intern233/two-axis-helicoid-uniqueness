import TwoAxisHelicoid.RemovableHarmonicPuncture
import TwoAxisHelicoid.DiskGreenModulus

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function InnerProductSpace
open scoped Topology ContDiff Manifold

/-- A bounded error in the logarithmic singularity suffices. Its
harmonic extension is constructed and fixes the multiplicity of the
zero used for the Green coordinate. -/
theorem green_modulus_of_logarithmic_potential {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (p : M) (u : M → ℝ) (negative : ∀ x, x≠p → u x<0)
    (boundary : Tendsto u (cocompact M) (𝓝 0)) (harm : ∀ x, x≠p → SurfaceHarmonicGerm u x)
    {C : ℝ} (bounded : ∀ᶠ z in 𝓝[≠] (chartAt ℂ p p),
      |u ((chartAt ℂ p).symm z)-Real.log ‖z-chartAt ℂ p p‖|≤C) :
    ∃ ρ : M → ℝ, IsDiskGreenModulus p ρ ∧ ∀ x, x≠p → ρ x=Real.exp (u x) := by
  classical
  let e := chartAt ℂ p
  let a := e p
  have ps : p∈e.source := mem_chart_source ℂ p
  have atgt : a∈e.target := e.map_source ps
  have chart := IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ,ℂ)) (n:=ω) p
  have away {z : ℂ} (ht : z∈e.target) (ne : z≠a) : e.symm z≠p := fun eq =>
    ne ((e.right_inv ht).symm.trans (congrArg e eq))
  let v := fun z => u (e.symm z)-Real.log ‖z-a‖
  have hv : ∀ᶠ z in 𝓝[≠] a, HarmonicAt v z := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds atgt)] with z nz ht
    have h := (surface_harmonic_germ_in_chart chart (e.map_target ht)).mp (harm _ (away ht nz))
    rw [e.right_inv ht] at h
    exact h.sub ((analyticAt_id.sub (analyticAt_const (v:=a))).harmonicAt_log_norm (sub_ne_zero.mpr nz))
  obtain ⟨g,hg,agree⟩ := bounded_harmonic_puncture_removable hv bounded
  let ρ := fun x => if x=p then 0 else Real.exp (u x)
  have eq (x : M) (ne : x≠p) : ρ x=Real.exp (u x) := ite_eq_right ne
  have zero : ρ p=0 := ite_eq_left rfl
  refine ⟨ρ,⟨fun x => ?_,fun x => ?_,fun x => ?_,?_,?_,g,hg,?_⟩,eq⟩
  · by_cases ne : x=p
    · simp only [ne,zero,le_refl]
    · exact (eq x ne).symm ▸ (Real.exp_pos _).le
  · by_cases ne : x=p
    · simp only [ne,zero,zero_lt_one]
    · exact (eq x ne).trans_lt (Real.exp_lt_one_iff.mpr (negative x ne))
  · by_cases ne : x=p
    · simp only [ne,zero]
    · simp only [eq x ne,Real.exp_ne_zero,ne]
  · have lim := Real.continuous_exp.continuousAt.tendsto.comp boundary
    rw [Real.exp_zero] at lim
    apply lim.congr'
    filter_upwards [(isCompact_singleton (x:=p)).compl_mem_cocompact] with x ne using (eq x ne).symm
  · intro x xp
    let f := chartAt ℂ x
    have xs : x∈f.source := mem_chart_source ℂ x
    have back : Tendsto f.symm (𝓝 (f x)) (𝓝 x) := by simpa only [f.left_inv xs] using (f.symm.continuousAt (f.map_source xs)).tendsto
    apply (harmonicAt_congr_nhds (f₂:=u ∘ f.symm) ?_).mpr
      ((surface_harmonic_germ_in_chart (IsManifold.chart_mem_maximalAtlas x) xs).mp (harm x xp))
    filter_upwards [back.eventually (isOpen_ne.mem_nhds xp)] with z ne
    rw [eq _ ne,Real.log_exp,comp_apply]
  · have punct : ∀ᶠ z in 𝓝[≠] a, ρ (e.symm z)=‖z-a‖*Real.exp (g z) := by
      filter_upwards [agree,self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds atgt)] with z same ne ht
      have val : u (e.symm z)=Real.log ‖z-a‖+g z := by change u (e.symm z)-Real.log ‖z-a‖=g z at same; linarith
      rw [eq _ (away ht ne),val,Real.exp_add,Real.exp_log (norm_pos_iff.mpr (sub_ne_zero.mpr ne))]
    filter_upwards [eventually_nhdsWithin_iff.mp punct] with z hz
    by_cases ne : z=a
    · subst z
      change ρ (e.symm (e p))=‖e p-e p‖*Real.exp (g (e p))
      rw [e.left_inv ps,zero,sub_self,norm_zero,zero_mul]
    · exact hz ne

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.green_modulus_of_logarithmic_potential
