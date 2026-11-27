import TwoAxisHelicoid.RemovableGerms

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- The periodic pole set determined by finitely many representatives. -/
def latticePoleSet (L : PeriodPair) (A : Set ℂ) : Set ℂ :=
  {z | ∃ a ∈ A, z-a ∈ L.lattice}

theorem latticePoleSet_countable (L : PeriodPair) {A : Set ℂ} (hA : A.Countable) :
    (latticePoleSet L A).Countable := by
  have hL : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have he : latticePoleSet L A = ⋃ a ∈ A, (fun z : ℂ => z-a) ⁻¹' (L.lattice : Set ℂ) := by
    ext z
    simp only [latticePoleSet,mem_ofPred_eq,mem_iUnion,mem_preimage,exists_prop]
    constructor <;> rintro ⟨a,ha,h⟩ <;> exact ⟨a,ha,h⟩
  rw [he]
  exact hA.biUnion (fun a _ => hL.preimage (sub_left_injective))

theorem latticePoleSet_isClosed (L : PeriodPair) {A : Set ℂ} (hA : A.Finite) :
    IsClosed (latticePoleSet L A) := by
  have he : latticePoleSet L A = ⋃ a ∈ A, (fun z : ℂ => z-a) ⁻¹' (L.lattice : Set ℂ) := by
    ext z
    simp only [latticePoleSet,mem_ofPred_eq,mem_iUnion,mem_preimage,exists_prop]
    constructor <;> rintro ⟨a,ha,h⟩ <;> exact ⟨a,ha,h⟩
  rw [he]
  exact hA.isClosed_biUnion (fun a _ => L.isClosed_lattice.preimage (by fun_prop))

theorem latticePoleSet_add_iff (L : PeriodPair) (A : Set ℂ) (z ω : ℂ)
    (hω : ω ∈ L.lattice) : z+ω ∈ latticePoleSet L A ↔ z ∈ latticePoleSet L A := by
  constructor
  · rintro ⟨a,ha,h⟩
    have he : (z+ω-a)-ω = z-a := by ring
    exact ⟨a,ha,he ▸ L.lattice.sub_mem h hω⟩
  · rintro ⟨a,ha,h⟩
    have he : (z-a)+ω = z+ω-a := by ring
    exact ⟨a,ha,he ▸ L.lattice.add_mem h hω⟩

theorem latticePoleSet_punctured_avoids (L : PeriodPair) {A : Set ℂ} (hA : A.Finite) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, w ∉ latticePoleSet L A := by
  have he : ∀ᶠ w in 𝓝 z, ∀ a ∈ A, w-a ∈ L.lattice → w = z := by
    apply (hA.eventually_all).mpr
    intro a _
    have hcont : Tendsto (fun w : ℂ => w-a) (𝓝 z) (𝓝 (z-a)) :=
      (show Continuous (fun w : ℂ => w-a) by fun_prop).continuousAt
    filter_upwards [hcont (L.compl_lattice_sdiff_singleton_mem_nhds (z-a))] with w hw hm
    by_contra hwz
    exact hw ⟨hm,by simpa only [mem_singleton_iff,sub_left_inj] using hwz⟩
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hwz
  rintro ⟨a,ha,hm⟩
  exact hwz (hw a ha hm)

/-- A removable germ at one pole propagates to every lattice translate,
using periodicity only at regular points. -/
theorem latticePoleSet_translate_germ (L : PeriodPair) {A : Set ℂ} (hA : A.Finite)
    {f g : ℂ → ℂ} {a ω : ℂ} (hω : ω ∈ L.lattice)
    (hp : ∀ z ω, ω ∈ L.lattice → z ∉ latticePoleSet L A → f (z+ω) = f z)
    (hg : AnalyticAt ℂ g a) (he : f =ᶠ[𝓝[≠] a] g) :
    ∃ g' : ℂ → ℂ, AnalyticAt ℂ g' (a+ω) ∧ f =ᶠ[𝓝[≠] (a+ω)] g' := by
  refine ⟨fun z => g (z-ω),?_,?_⟩
  · have hg' : AnalyticAt ℂ g ((a+ω)-ω) := by simpa only [add_sub_cancel_right] using hg
    exact hg'.comp (f := fun z : ℂ => z-ω) (by fun_prop)
  · have hshift : Tendsto (fun z : ℂ => z-ω) (𝓝[≠] (a+ω)) (𝓝[≠] a) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have h : Tendsto (fun z : ℂ => z-ω) (𝓝 (a+ω)) (𝓝 a) := by
          simpa only [add_sub_cancel_right] using
            (show Continuous (fun z : ℂ => z-ω) by fun_prop).continuousAt.tendsto (x := a+ω)
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa only [mem_compl_iff,mem_singleton_iff,sub_eq_iff_eq_add] using hz
    filter_upwards [hshift.eventually he,
      hshift.eventually (latticePoleSet_punctured_avoids L hA a)] with z hz hn
    calc
      f z = f ((z-ω)+ω) := by rw [sub_add_cancel]
      _ = f (z-ω) := hp (z-ω) ω hω hn
      _ = g (z-ω) := hz

theorem elliptic_finite_principal_parts_constant (L : PeriodPair) {A : Set ℂ}
    (hA : A.Finite) {f : ℂ → ℂ}
    (hf : ∀ z ∉ latticePoleSet L A, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ L.lattice → z ∉ latticePoleSet L A → f (z+ω) = f z)
    (hloc : ∀ a ∈ A, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ f =ᶠ[𝓝[≠] a] g) :
    ∃ c : ℂ, ∀ z ∉ latticePoleSet L A, f z = c := by
  apply elliptic_removable_germs_constant L (latticePoleSet_countable L hA.countable)
    (fun z ω hω hz => (latticePoleSet_add_iff L A z ω hω).not.mpr hz) hf hp
  rintro z ⟨a,ha,hω⟩
  obtain ⟨g,hg,he⟩ := hloc a ha
  have h := latticePoleSet_translate_germ L hA hω hp hg he
  have heq : a+(z-a) = z := by ring
  rwa [heq] at h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.elliptic_finite_principal_parts_constant
