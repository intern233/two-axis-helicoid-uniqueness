import TwoAxisHelicoid.SurfaceHarmonicSandwich
import TwoAxisHelicoid.LogarithmicGreenPotential
import TwoAxisHelicoid.OpenSurfaceHarmonicGerms
import TwoAxisHelicoid.HolomorphicBoundaryBarrier

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

def openSurfacePuncture {M : Type*} [TopologicalSpace M] [T1Space M] (p : M) : Opens M :=
  ⟨{p}ᶜ,isClosed_singleton.isOpen_compl⟩

/-- The strong maximum principle on a connected surface makes a
nonpositive harmonic function strictly negative if it is negative once. -/
theorem harmonic_negative_of_one_negative {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {h : M → ℝ} (harm : ∀ x, SurfaceHarmonicGerm h x)
    (nonpos : ∀ x, h x≤0) (some : ∃ x, h x<0) : ∀ x, h x<0 := by
  let S := h ⁻¹' {0}
  have ch : Continuous h := continuous_iff_continuousAt.mpr fun x => (harm x).subharmonicAt.1
  have closed : IsClosed S := isClosed_singleton.preimage ch
  have op : IsOpen S := isOpen_iff_mem_nhds.mpr (by
    intro x hx
    have zero : h x=0 := hx
    have loc : IsLocalMax (fun y => h y-(0:ℝ)) x := .of_forall fun y => by simpa only [sub_zero,zero] using nonpos y
    filter_upwards [(harm x).subharmonicAt.2 _ (surface_harmonic_const 0 x) loc] with y hy
    change h y=0
    simpa only [sub_zero,zero] using hy)
  obtain ⟨w,neg⟩ := some
  have empty := (isClopen_iff.mp (show IsClopen S from ⟨closed,op⟩)).resolve_right (fun all => neg.ne (show w∈S from all.symm ▸ mem_univ w))
  exact fun x => lt_of_le_of_ne (nonpos x) (fun eq => (nonempty_of_mem (show x∈S from eq)).ne_empty empty)

/-- The Perron envelope yields a genuine Green function when a single
superharmonic logarithmic cap, a lower logarithmic subfunction, and
boundary barriers are available. Boundary subfunctions may depend on
the boundary point and requested accuracy. -/
theorem green_modulus_from_perron_barriers {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (p : M) [PreconnectedSpace (openSurfacePuncture p)] [NoncompactSpace (openSurfacePuncture p)]
    (L H : openSurfacePuncture p → ℝ) (lo : ∀ x, SurfaceSubharmonicAt L x)
    (hi : ∀ x, SurfaceSubharmonicAt (fun y => -H y) x) (order : L≤H)
    (nonpos : ∀ x, H x≤0) (some : ∃ x, H x<0) {C : ℝ}
    (logBounds : ∀ᶠ z in 𝓝[≠] (chartAt ℂ p p), let x := (chartAt ℂ p).symm z
      Real.log ‖z-chartAt ℂ p p‖-C ≤ openSetExtension (openSurfacePuncture p) L x ∧
      openSetExtension (openSurfacePuncture p) H x ≤ Real.log ‖z-chartAt ℂ p p‖+C)
    (barriers : ∀ ε>0, ∀ᶠ x in cocompact M, ∃ f : openSurfacePuncture p → ℝ,
      (∀ w, SurfaceSubharmonicAt f w) ∧ f≤H ∧ -ε<openSetExtension (openSurfacePuncture p) f x) :
    ∃ ρ : M → ℝ, IsDiskGreenModulus p ρ := by
  let V := openSurfacePuncture p
  obtain ⟨h,harm,up,greatest⟩ := greatest_harmonic_minorant_of_superharmonic lo hi order
  have lower := greatest L lo order
  have neg := harmonic_negative_of_one_negative harm (fun x => (up x).trans (nonpos x)) (some.imp fun x hx => (up x).trans_lt hx)
  let u := openSetExtension V h
  have eq (x : M) (ne : x≠p) : u x=h ⟨x,ne⟩ := openSetExtension_val V h ⟨x,ne⟩
  have endLim : Tendsto u (cocompact M) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    filter_upwards [barriers ε ep,(isCompact_singleton (x:=p)).compl_mem_cocompact] with x ex ne
    obtain ⟨f,sf,fh,good⟩ := ex
    let w : V := ⟨x,ne⟩
    rw [show openSetExtension (openSurfacePuncture p) f x=f w from openSetExtension_val V f w] at good
    rw [Real.dist_eq,sub_zero,eq x ne,abs_of_neg (neg w)]
    linarith [greatest f sf fh w]
  have hn (x : M) (ne : x≠p) : SurfaceHarmonicGerm u x :=
    (surface_harmonic_germ_open_subtype V ⟨x,ne⟩ u).mpr (by simpa only [u,openSetExtension_val] using harm (⟨x,ne⟩ : V))
  obtain ⟨ρ,hρ,_⟩ := green_modulus_of_logarithmic_potential p u (fun x ne => (eq x ne).trans_lt (neg _)) endLim hn (C:=C) (by
    let e := chartAt ℂ p
    have ps : p∈e.source := mem_chart_source ℂ p
    filter_upwards [logBounds,self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds (e.map_source ps))] with z hz ne ht
    have nz : e.symm z≠p := fun same => ne ((e.right_inv ht).symm.trans (congrArg e same))
    let w : V := ⟨e.symm z,nz⟩
    have l : openSetExtension V L (e.symm z)=L w := openSetExtension_val V L w
    have r : openSetExtension V H (e.symm z)=H w := openSetExtension_val V H w
    change Real.log ‖z-e p‖-C≤openSetExtension V L (e.symm z) ∧ openSetExtension V H (e.symm z)≤Real.log ‖z-e p‖+C at hz
    rw [l,r] at hz
    change |u (e.symm z)-Real.log ‖z-e p‖|≤C
    rw [eq _ nz,abs_le]
    constructor <;> linarith [lower w,up w,hz.1,hz.2])
  exact ⟨ρ,hρ⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.green_modulus_from_perron_barriers
