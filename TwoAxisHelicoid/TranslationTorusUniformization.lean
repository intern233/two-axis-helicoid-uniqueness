import TwoAxisHelicoid.SimplyConnectedLocalPrimitives
import TwoAxisHelicoid.PeriodicPlaneDevelopment
import TwoAxisHelicoid.CompactPlaneCoverUniformization
import Mathlib.Topology.LocallyConstant.Basic

namespace TwoAxisHelicoid
open Complex Set Filter Topology Function
open scoped Topology ContDiff Manifold

/-- An atlas of local holomorphic primitives of a nonvanishing
differential. The differences of two such coordinates are locally
constant on each component of their common domain. -/
structure HolomorphicTranslationCoordinates (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M] where
  coord : M → OpenPartialHomeomorph M ℂ
  member : ∀ x, coord x∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M
  centered : ∀ x, x∈(coord x).source
  translations : ∀ i j x, x∈(coord i).source∩(coord j).source →
    ∀ᶠ y in 𝓝 x, coord i y-coord j y=coord i x-coord j x

private theorem local_homeomorph_of_coordinate_germs {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (charts : ∀ x : X, ∃ e : OpenPartialHomeomorph X Y, x∈e.source ∧ f=ᶠ[𝓝 x] e) : IsLocalHomeomorph f := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨e,hx,eq⟩ := charts x
  obtain ⟨U,sub,op,hU⟩ := mem_nhds_iff.mp (inter_mem (e.open_source.mem_nhds hx) eq)
  have inside : U⊆e.source := fun y hy => (sub hy).1
  have same : U.domRestrict f=U.domRestrict e := funext fun y => (sub y.2).2
  refine ⟨U,op.mem_nhds hU,same ▸ ?_⟩
  exact e.isOpenEmbedding_restrict.comp (Topology.IsOpenEmbedding.inclusion inside (op.preimage continuous_subtype_val))

private theorem translated_chart_analytic {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {e : OpenPartialHomeomorph M ℂ}
    (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (b : ℂ) :
    e.trans (Homeomorph.addRight b).toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · intro x hx
    exact ((contMDiffAt_of_mem_maximalAtlas he hx.1).add contMDiffAt_const).contMDiffWithinAt
  · intro w hw
    exact ((contMDiffAt_symm_of_mem_maximalAtlas he hw.2).comp w (contMDiffAt_id.add contMDiffAt_const)).contMDiffWithinAt

/-- On a compact topological torus the existence of holomorphic
translation coordinates gives the actual complex torus uniformization
without the simply connected uniformization theorem. -/
theorem compact_torus_uniformization_of_translation_coordinates {M : Type*} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    {L : PeriodPair} (mark : M ≃ₜ PeriodTorus L) (A : HolomorphicTranslationCoordinates M) :
    AdmitsPeriodTorusUniformization M := by
  let p := mark.symm ∘ periodTorusProjection L
  have pc : IsCoveringMap p := (periodTorusProjection_isCoveringMap L).homeomorph_comp mark.symm
  have sur : Surjective p := mark.symm.surjective.comp (Quotient.mk_surjective : Surjective (periodTorusProjection L))
  let U := fun i => p ⁻¹' (A.coord i).source
  let f := fun i => A.coord i ∘ p
  obtain ⟨D,prim⟩ := simply_connected_glue_local_primitives (0:ℂ) U
    (fun i => (A.coord i).open_source.preimage pc.continuous) p (fun z => A.centered (p z)) f
    (fun i j x hx => pc.continuous.continuousAt.tendsto.eventually (A.translations i j (p x) hx))
  have germ (i : M) (z : ℂ) (inside : p z∈(A.coord i).source) :
      D=ᶠ[𝓝 z] fun w => A.coord i (p w)+(D z-A.coord i (p z)) := by
    filter_upwards [prim i z inside] with y hy
    change D y-A.coord i (p y)=D z-A.coord i (p z) at hy
    exact (sub_eq_iff_eq_add.mp hy).trans (add_comm _ _)
  have localD : IsLocalHomeomorph D := by
    apply local_homeomorph_of_coordinate_germs
    intro z
    obtain ⟨l,hz,eq⟩ := pc.isLocalHomeomorph z
    let a := A.coord (p z)
    let c := D z-a (p z)
    let e := (l.trans a).trans (Homeomorph.addRight c).toOpenPartialHomeomorph
    have source : z∈e.source := ⟨⟨hz,eq ▸ A.centered (p z)⟩,trivial⟩
    refine ⟨e,source,?_⟩
    filter_upwards [germ (p z) z (A.centered _)] with w hw
    change D w=a (l w)+c
    rwa [← eq]
  have shiftp (i : Fin 2) (z : ℂ) : p (z+L.basis i)=p z := by
    apply congrArg mark.symm
    apply (periodTorusProjection_eq_iff L _ _).mpr
    have h : L.basis i∈L.lattice := by fin_cases i <;> simp [L.ω₁_mem_lattice,L.ω₂_mem_lattice]
    rw [show z-(z+L.basis i)= -L.basis i by abel]
    exact L.lattice.neg_mem h
  let δ := fun (i : Fin 2) z => D (z+L.basis i)-D z
  have mon (i : Fin 2) : IsLocallyConstant (δ i) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    have tar : p (z+L.basis i)∈(A.coord (p z)).source := by rw [shiftp]; exact A.centered _
    have shift : Tendsto (fun w : ℂ => w+L.basis i) (𝓝 z) (𝓝 (z+L.basis i)) := (continuous_id.add continuous_const).continuousAt
    filter_upwards [shift.eventually (germ (p z) (z+L.basis i) tar),germ (p z) z (A.centered _)] with w hw hd
    change D (w+L.basis i)=A.coord (p z) (p (w+L.basis i))+(D (z+L.basis i)-A.coord (p z) (p (z+L.basis i))) at hw
    change D (w+L.basis i)-D w=D (z+L.basis i)-D z
    rw [hw,hd,shiftp,shiftp]
    abel
  obtain ⟨Φ,hΦ⟩ := periodic_local_development_is_homeomorph L localD (fun i => δ i 0) (fun i z =>
    (sub_eq_iff_eq_add.mp ((mon i).apply_eq_of_isPreconnected isPreconnected_univ (mem_univ z) (mem_univ 0))).trans (add_comm _ _))
  have ep (w : ℂ) : D (Φ.symm w)=w := hΦ ▸ Φ.apply_symm_apply w
  apply compact_surface_uniformizes_of_holomorphic_plane_cover (p := p ∘ Φ.symm)
  refine ⟨pc.comp_homeomorph Φ.symm,sur.comp Φ.symm.surjective,?_⟩
  intro w
  let z := Φ.symm w
  let e := A.coord (p z)
  let c := D z-e (p z)
  let a := e.trans (Homeomorph.addRight c).toOpenPartialHomeomorph
  have h : p z∈e.source := A.centered _
  have eq : w=e (p z)+c := by change w=e (p z)+(D (Φ.symm w)-e (p z)); rw [ep]; abel
  have target : w∈a.target := by
    refine ⟨trivial,?_⟩
    change w+-c∈e.target
    rw [eq,add_neg_cancel_right]
    exact e.map_source h
  refine ⟨a,translated_chart_analytic (A.member _) c,target,?_⟩
  have clos : Tendsto Φ.symm (𝓝 w) (𝓝 z) := Φ.symm.continuous.continuousAt
  filter_upwards [clos.eventually (germ (p z) z h),clos.eventually (pc.continuous.continuousAt.eventually (e.open_source.mem_nhds h))] with v hv hs
  have E : v=e (p (Φ.symm v))+c := (ep v).symm.trans hv
  change e.symm (v+-c)=p (Φ.symm v)
  exact (congrArg e.symm (by simpa only [add_neg_cancel_right] using congrArg (fun u : ℂ => u+-c) E)).trans (e.left_inv hs)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_torus_uniformization_of_translation_coordinates
