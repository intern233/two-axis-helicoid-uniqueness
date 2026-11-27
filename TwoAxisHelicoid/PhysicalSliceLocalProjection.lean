import TwoAxisHelicoid.PhysicalCoreTubeProjection
import TwoAxisHelicoid.PhysicalTubeFootCharts

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- Test local invertibility in an embedded moving parameter domain,
using forward germs alone. Neither inverse chart extension outside
the slice nor a marking of individual sheets is prescribed. -/
theorem surface_projection_of_forward_chart_germs {A B M : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace M] {p : A → B} {j : A → M} (cp : Continuous p) (oj : IsOpenEmbedding j)
    (germs : ∀ q, ∃ (a : OpenPartialHomeomorph M ℂ) (b : OpenPartialHomeomorph B ℂ)
      (g : OpenPartialHomeomorph ℂ ℂ), j q∈a.source ∧ p q∈b.source ∧ a (j q)∈g.source ∧
      (b ∘ p) =ᶠ[𝓝 q] g ∘ a ∘ j) : IsLocalHomeomorph p := by
  apply local_homeomorph_of_surface_chart_germs cp
  intro q
  let _ : Nonempty A := ⟨q⟩
  obtain ⟨a,b,g,qa,qb,qg,eq⟩ := germs q
  let i := oj.toOpenPartialHomeomorph j
  let s := i.trans a
  have qi : q∈i.source := by change q∈(oj.toOpenPartialHomeomorph j).source; rw [oj.toOpenPartialHomeomorph_source]; trivial
  have sq : q∈s.source := ⟨qi,qa⟩
  refine ⟨s,b,g,sq,qb,qg,?_⟩
  have back : Tendsto s.symm (𝓝 (s q)) (𝓝 q) := by
    simpa only [s.left_inv sq] using (s.symm.continuousAt (s.map_source sq)).tendsto
  filter_upwards [back.eventually eq,s.open_target.mem_nhds (s.map_source sq)] with z hz zt
  change b (p (s.symm z))=g (s (s.symm z)) at hz
  simpa only [Function.comp_apply,s.right_inv zt] using hz

/-- The normal-tube projection is a local homeomorphism on the actual
moving surface whenever its chart normals make a transverse angle with
the reference normal. Both physical parameter domains can be arbitrary. -/
theorem physical_tube_slice_local_homeomorph {B M : Type*} [TopologicalSpace B] [TopologicalSpace M]
    {V : Set B} (vo : IsOpen V) {X N : B → SurfaceEuclideanSpace} {Y : M → SurfaceEuclideanSpace}
    (emb : IsEmbedding Y) {r : ℝ} :
    let T := fun q : V × ℝ => X q.1.1+q.2 • N q.1.1
    IsOpenEmbedding (({q : V × ℝ | |q.2|<r}).domRestrict T) →
    (∀ q∈spatialTubeSlice T (range Y) r, HasPhysicalTubeFootChart X N (q.1.1,q.2)) →
    (∀ q∈spatialTubeSlice T (range Y) r, ∀ y, Y y=T q → ∃ (a : OpenPartialHomeomorph M ℂ) (m : SurfaceEuclideanSpace),
      y∈a.source ∧ ContDiffAt ℝ 1 (Y ∘ a.symm) (a y) ∧ Function.Injective (fderiv ℝ (Y ∘ a.symm) (a y)) ∧
      ‖m‖=1 ∧ (∀ v, ⟪fderiv ℝ (Y ∘ a.symm) (a y) v,m⟫=0) ∧ coreNormalDistance m (N q.1.1)<1) →
    IsLocalHomeomorph (fun q : spatialTubeSlice T (range Y) r => q.1.1) := by
  intro T tube foot sheets
  let D := spatialTubeSlice T (range Y) r
  let p := fun q : D => q.1.1
  obtain ⟨j,oj,space⟩ := physical_tube_slice_open_marking tube emb
  apply surface_projection_of_forward_chart_germs (p := p) (continuous_fst.comp continuous_subtype_val) oj
  intro q
  let _ : Nonempty V := ⟨p q⟩
  obtain ⟨b,f,qb,identity,trans⟩ := foot q.1 q.2
  obtain ⟨a,m,qa,sa,imm,unit,orth,tilt⟩ := sheets q.1 q.2 (j q) (space q)
  let k := vo.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : V → B)
  let d := k.trans b
  have kd : p q∈k.source := by change p q∈(vo.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph _).source; rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source]; trivial
  have pos : (Y ∘ a.symm) (a (j q))=T q.1 := by rw [Function.comp_apply,a.left_inv qa,space]
  obtain ⟨g,inside,ge,_⟩ := trans (Y ∘ a.symm) (a (j q)) pos sa imm m unit orth tilt
  refine ⟨a,d,g,qa,⟨kd,qb⟩,inside,?_⟩
  let inc := fun u : D => ((p u).1,u.1.2)
  have continuousInc : Continuous inc := (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp continuous_subtype_val)
  filter_upwards [continuousInc.continuousAt.tendsto.eventually identity,oj.continuous.continuousAt.preimage_mem_nhds
    (a.open_source.mem_nhds qa)] with u eq au
  change b (p u).1=f (T u.1) at eq
  change b (p u).1=g (a (j u))
  rw [ge,Function.comp_apply,Function.comp_apply,a.left_inv au,space,eq]

/-- Restrict the embedded physical tube to an arbitrary smaller open
base and a smaller interval, retaining its actual coordinate map. -/
theorem compact_core_subtube_open_embedding {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]
    {T : B × ℝ → E} {V U : Set B} {r R : ℝ} (vo : IsOpen V) (sub : V⊆U) (small : R≤r)
    (tube : IsOpenEmbedding ((U ×ˢ Metric.ball (0:ℝ) r).domRestrict T)) :
    let TV := fun q : V × ℝ => T (q.1.1,q.2)
    IsOpenEmbedding (({q : V × ℝ | |q.2|<R}).domRestrict TV) := by
  let W := {q : V × ℝ | |q.2|<R}
  let full := U ×ˢ Metric.ball (0:ℝ) r
  let inc := fun q : W => ((q.1.1.1,q.1.2) : B × ℝ)
  have base : IsOpenEmbedding (Prod.map (Subtype.val : V → B) (id : ℝ → ℝ)) :=
    vo.isOpenEmbedding_subtypeVal.prodMap .id
  have op : IsOpen W := isOpen_lt continuous_snd.abs continuous_const
  have oi : IsOpenEmbedding inc := base.comp op.isOpenEmbedding_subtypeVal
  have membership (q : W) : inc q∈full :=
    ⟨sub q.1.1.2,by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using q.2.trans_le small⟩
  let j := Set.codRestrict inc full membership
  have cj : Continuous j := oi.continuous.subtype_mk _
  have oj : IsOpenEmbedding j := .of_continuous_injective_isOpenMap cj
    (fun x y eq => oi.injective (congrArg Subtype.val eq)) (oi.isOpenMap.codRestrict membership)
  exact tube.comp oj

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.surface_projection_of_forward_chart_germs
#print axioms TwoAxisHelicoid.physical_tube_slice_local_homeomorph
#print axioms TwoAxisHelicoid.compact_core_subtube_open_embedding
