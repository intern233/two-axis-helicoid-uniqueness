import TwoAxisHelicoid.CompactCoreTransverseCoordinates
import TwoAxisHelicoid.CoreSheetPlaneConvergence

namespace TwoAxisHelicoid
open Set Filter Metric Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- A local coordinate for the foot of the physical normal tube, with
an inverse for every immersed moving sheet transverse to the normal
fiber at this very point. All chart identities are local germs. -/
def HasPhysicalTubeFootChart {B : Type*} [TopologicalSpace B] (X N : B → SurfaceEuclideanSpace)
    (q : B × ℝ) : Prop :=
  let T := fun v : B × ℝ => X v.1+v.2 • N v.1
  ∃ (a : OpenPartialHomeomorph B ℂ) (f : SurfaceEuclideanSpace → ℂ),
    q.1∈a.source ∧ (a ∘ Prod.fst) =ᶠ[𝓝 q] f ∘ T ∧
    ∀ (Y : ℂ → SurfaceEuclideanSpace) (w : ℂ), Y w=T q → ContDiffAt ℝ 1 Y w →
      Function.Injective (fderiv ℝ Y w) → ∀ m : SurfaceEuclideanSpace,
      ‖m‖=1 → (∀ v, ⟪fderiv ℝ Y w v,m⟫=0) → coreNormalDistance m (N q.1)<1 →
      ∃ g : OpenPartialHomeomorph ℂ ℂ, w∈g.source ∧ (g : ℂ → ℂ)=f ∘ Y ∧
        ContDiffAt ℝ 1 (Y ∘ g.symm) (f (Y w))

/-- Tangent-plane transversality and the actual normal coordinate
inverse hold on a neighborhood of each zero-height foot. -/
theorem physical_foot_charts_near_zero {B : Type*} [TopologicalSpace B] {X N : B → SurfaceEuclideanSpace}
    {b : B} (a : OpenPartialHomeomorph B ℂ) (ba : b∈a.source)
    (sx : ContDiffAt ℝ 1 (X ∘ a.symm) (a b)) (sn : ContDiffAt ℝ 1 (N ∘ a.symm) (a b))
    (inj : Function.Injective (fderiv ℝ (X ∘ a.symm) (a b))) (unit : ‖N b‖=1)
    (orth : ∀ v, ⟪fderiv ℝ (X ∘ a.symm) (a b) v,N b⟫=0) :
    ∀ᶠ q in 𝓝 (b,(0:ℝ)), HasPhysicalTubeFootChart X N q := by
  let Y := X ∘ a.symm
  let n := N ∘ a.symm
  let T := fun q : B × ℝ => X q.1+q.2 • N q.1
  let k := fun q : B × ℝ => (a q.1,q.2)
  obtain ⟨e,start,formula,sm⟩ := normal_coordinate_smooth_local_inverse (X := Y) (N := n) sx sn inj
    (by simpa only [n,Function.comp_apply,a.left_inv ba] using unit)
    (fun v => by simpa only [n,Function.comp_apply,a.left_inv ba] using orth v)
  let f := Prod.fst ∘ e.symm
  let h := Prod.snd ∘ e.symm
  have kz : ContinuousAt k (b,(0:ℝ)) := ((a.continuousAt ba).comp continuous_fst.continuousAt).prodMk continuous_snd.continuousAt
  have first : ∀ᶠ q in 𝓝 (b,(0:ℝ)), q.1∈a.source :=
    (continuous_fst.continuousAt (x := (b,(0:ℝ)))).preimage_mem_nhds (a.open_source.mem_nhds ba)
  have contact : ∀ᶠ q in 𝓝 (b,(0:ℝ)), q.1∈a.source ∧ k q∈e.source :=
    first.and (kz.preimage_mem_nhds (e.open_source.mem_nhds start))
  obtain ⟨U,safe,op,center⟩ := mem_nhds_iff.mp contact
  have forward {q : B × ℝ} (hq : q∈U) : e (k q)=T q := by
    rw [formula]
    simp only [k,Y,n,Function.comp_apply,a.left_inv (safe hq).1,T]
  have back {q : B × ℝ} (hq : q∈U) : e.symm (T q)=k q := by rw [← forward hq,e.left_inv (safe hq).2]
  have ce : ContinuousAt (e ∘ k) (b,(0:ℝ)) := (e.continuousAt start).comp (f := k) kz
  have equal : (e ∘ k) =ᶠ[𝓝 (b,(0:ℝ))] T := Filter.mem_of_superset (op.mem_nhds center) (fun _ hq => forward hq)
  have ct : ContinuousAt T (b,(0:ℝ)) := ce.congr equal
  have sm0 : ContDiffAt ℝ 1 e.symm (T (b,0)) := by simpa only [Y,T,Function.comp_apply,a.left_inv ba,zero_smul,add_zero] using sm
  have ca : ContinuousAt (a ∘ (Prod.fst : B × ℝ → B)) (b,0) := (a.continuousAt ba).comp continuous_fst.continuousAt
  filter_upwards [op.mem_nhds center,ct.tendsto.eventually (sm0.eventually (by simp)),
    ca.tendsto.eventually (sx.eventually (by simp)),ca.tendsto.eventually (sn.eventually (by simp))] with q hq reg ax an
  refine ⟨a,f,(safe hq).1,?_,?_⟩
  · filter_upwards [op.mem_nhds hq] with u hu
    exact (congrArg Prod.fst (back hu)).symm
  · intro Z w pos smooth imm m un perp close
    change Z w=T q at pos
    have foot : f (Z w)=a q.1 := pos ▸ congrArg Prod.fst (back hq)
    have normalize : n (f (Z w))=N q.1 := by simp only [foot,n,Function.comp_apply,a.left_inv (safe hq).1]
    have near : ‖N q.1-m‖<1 ∨ ‖N q.1+m‖<1 := by
      simpa only [coreNormalDistance,norm_sub_rev (N q.1) m,add_comm (N q.1) m,min_lt_iff] using close
    have rz : ContDiffAt ℝ 1 e.symm (Z w) := pos ▸ reg
    have dx : DifferentiableAt ℝ Y (f (Z w)) := by rw [foot]; exact ax.differentiableAt (by simp)
    have dn : DifferentiableAt ℝ n (f (Z w)) := by rw [foot]; exact an.differentiableAt (by simp)
    apply transverse_core_normal_sheet (X := Y) (N := n) (base := f) (height := h) dx dn
      (contDiffAt_fst.comp _ rz) ((contDiffAt_snd.comp _ rz).differentiableAt (by simp)) _ smooth imm m perp
      (normalize ▸ nearby_core_normals_transverse un near)
    have image : Z w∈e.target := (pos.trans (forward hq).symm) ▸ e.map_source (safe hq).2
    filter_upwards [e.open_target.mem_nhds image] with y hy
    have eq := e.right_inv hy
    rwa [formula] at eq

/-- The same positive height bound suffices simultaneously along a
compact core, including points on its boundary. -/
theorem compact_physical_foot_charts {B : Type*} [TopologicalSpace B] {X N : B → SurfaceEuclideanSpace}
    {K : Set B} (kc : IsCompact K)
    (regular : ∀ b∈K, ∃ a : OpenPartialHomeomorph B ℂ, b∈a.source ∧
      ContDiffAt ℝ 1 (X ∘ a.symm) (a b) ∧ ContDiffAt ℝ 1 (N ∘ a.symm) (a b) ∧
      Function.Injective (fderiv ℝ (X ∘ a.symm) (a b)) ∧ ‖N b‖=1 ∧
      ∀ v, ⟪fderiv ℝ (X ∘ a.symm) (a b) v,N b⟫=0) :
    ∃ r : ℝ, 0<r ∧ ∀ b∈K, ∀ t : ℝ, |t|<r → HasPhysicalTubeFootChart X N (b,t) := by
  let G := {q : B × ℝ | HasPhysicalTubeFootChart X N q}
  have sub : K ×ˢ ({0}:Set ℝ)⊆interior G := by
    rintro ⟨b,t⟩ ⟨hb,ht⟩
    change t=0 at ht
    subst t
    obtain ⟨a,ha,sx,sn,inj,un,orth⟩ := regular b hb
    exact mem_interior_iff_mem_nhds.mpr (physical_foot_charts_near_zero a ha sx sn inj un orth)
  obtain ⟨_,V,_,vo,kin,zin,both⟩ := generalized_tube_lemma kc isCompact_singleton isOpen_interior sub
  obtain ⟨r,rp,small⟩ := Metric.mem_nhds_iff.mp (vo.mem_nhds (zin (mem_singleton _)))
  refine ⟨r,rp,?_⟩
  intro b hb t ht
  have tv : t∈V := small (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
  change (b,t)∈G
  exact (interior_subset (s := G)) (both ⟨kin hb,tv⟩)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_foot_charts_near_zero
#print axioms TwoAxisHelicoid.compact_physical_foot_charts
