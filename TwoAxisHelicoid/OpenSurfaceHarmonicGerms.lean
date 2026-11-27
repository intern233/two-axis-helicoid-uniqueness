import TwoAxisHelicoid.SurfaceHarmonicComparison
import TwoAxisHelicoid.HolomorphicSubdomainCoordinate

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function TopologicalSpace
open scoped Topology ContDiff Manifold

/-- Ambient extension with the prescribed values on the open subdomain. -/
noncomputable def openSetExtension {M E : Type*} [TopologicalSpace M] [Zero E] (V : Opens M) (f : V → E) : M → E :=
  Function.extend Subtype.val f (fun _ => 0)

@[simp] theorem openSetExtension_val {M E : Type*} [TopologicalSpace M] [Zero E] (V : Opens M) (f : V → E) (x : V) :
    openSetExtension V f x.val=f x := Subtype.val_injective.extend_apply _ _ _

theorem eventually_open_subtype_val {M : Type*} [TopologicalSpace M] (V : Opens M) (x : V) (P : M → Prop) :
    (∀ᶠ y in 𝓝 x.val, P y) ↔ ∀ᶠ z in 𝓝 x, P z.val := by
  rw [← V.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x]
  rfl

theorem surface_harmonic_germ_open_subtype {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (V : Opens M) (x : V) (f : M → ℝ) :
    SurfaceHarmonicGerm f x.val ↔ SurfaceHarmonicGerm (fun y : V => f y.val) x := by
  constructor
  · rintro ⟨F,hF,eq⟩
    exact ⟨fun y => F y.val,contMDiffAt_subtype_iff.mpr hF,(eventually_open_subtype_val V x _).mp eq⟩
  · rintro ⟨F,hF,eq⟩
    let G := openSetExtension V F
    have hG : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y : V => G y.val) x := by simpa only [G,openSetExtension_val] using hF
    refine ⟨G,contMDiffAt_subtype_iff.mp hG,(eventually_open_subtype_val V x _).mpr ?_⟩
    simpa only [G,openSetExtension_val] using eq

theorem surface_subharmonic_open_subtype {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (V : Opens M) (x : V) {f : M → ℝ} (hf : SurfaceSubharmonicAt f x.val) :
    SurfaceSubharmonicAt (fun y : V => f y.val) x := by
  refine ⟨hf.1.comp continuous_subtype_val.continuousAt,?_⟩
  intro h hh mx
  let H := openSetExtension V h
  have hb : SurfaceHarmonicGerm H x.val := (surface_harmonic_germ_open_subtype V x H).mpr (by simpa only [H,openSetExtension_val] using hh)
  have m : IsLocalMax (fun z => f z-H z) x.val := (eventually_open_subtype_val V x _).mpr (by
    change ∀ᶠ y in 𝓝 x, f y.val-h y≤f x.val-h x at mx
    simpa only [H,openSetExtension_val] using mx)
  have eq := (eventually_open_subtype_val V x _).mp (hf.2 H hb m)
  simpa only [H,openSetExtension_val] using eq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.surface_subharmonic_open_subtype
