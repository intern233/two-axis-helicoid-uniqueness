import TwoAxisHelicoid.RegularCoreNormalCoordinates

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- The signed height on an actual uniform tube is continuous in the
open tube and continuously differentiable at every foot point for which
the normal chart is regular. The global height agrees with the same
local inverse that was obtained from the derivative of the immersion. -/
theorem compact_regular_core_signed_tube {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {X N : M → SurfaceEuclideanSpace} {K : Set M} (kc : IsCompact K) (embed : InjOn X K)
    (charts : ∀ p∈K, let e := chartAt ℂ p
      let z := e p
      ContDiffAt ℝ 1 (X ∘ e.symm) z ∧ ContDiffAt ℝ 1 (N ∘ e.symm) z ∧
        Function.Injective (fderiv ℝ (X ∘ e.symm) z) ∧ ‖N p‖=1 ∧ ∀ v, ⟪fderiv ℝ (X ∘ e.symm) z v,N p⟫=0) :
    ∃ (U : Set M) (r : ℝ) (signed : SurfaceEuclideanSpace → ℝ), IsOpen U ∧ K⊆U ∧ 0<r ∧
      let W := U ×ˢ ball (0:ℝ) r
      let J := W.domRestrict (fun a : M × ℝ => X a.1+a.2 • N a.1)
      IsOpenEmbedding J ∧ ContinuousOn signed (range J) ∧ (∀ q : W, signed (J q)=q.1.2) ∧
      ∀ p∈K, ContDiffAt ℝ 1 signed (X p) ∧ signed (X p)=0 := by
  classical
  obtain ⟨U,r,uo,ku,rp,emb⟩ := compact_immersed_core_normal_tube kc embed charts
  let W := U ×ˢ ball (0:ℝ) r
  let J := W.domRestrict (fun a : M × ℝ => X a.1+a.2 • N a.1)
  let H := emb.toIsEmbedding.toHomeomorph
  let signed := fun y => if hy : y∈range J then (H.symm ⟨y,hy⟩).1.2 else (0:ℝ)
  have value (q : W) : signed (J q)=q.1.2 := by
    change (if hy : J q∈range J then (H.symm ⟨J q,hy⟩).1.2 else (0:ℝ))=_
    rw [dite_eq_left (mem_range_self q)]
    exact congrArg (fun a : W => a.1.2) (H.symm_apply_apply q)
  have continuousHeight : ContinuousOn signed (range J) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have eq : (range J).domRestrict signed=(fun q : W => q.1.2) ∘ H.symm := by
      funext q
      simp only [domRestrict_apply,signed,dite_eq_left q.2,Function.comp_apply]
      rfl
    rw [eq]
    exact continuous_snd.comp (continuous_subtype_val.comp H.symm.continuous)
  refine ⟨U,r,signed,uo,ku,rp,emb,continuousHeight,value,?_⟩
  intro p hp
  let e := chartAt ℂ p
  let z := e p
  have ex : p∈e.source := mem_chart_source ℂ p
  have et : z∈e.target := e.map_source ex
  obtain ⟨sx,sn,inj,one,ort⟩ := charts p hp
  obtain ⟨d,inside,eq,sm⟩ := normal_coordinate_smooth_local_inverse (X := X ∘ e.symm) (N := N ∘ e.symm) (z := e p) sx sn inj
    (by simpa only [Function.comp_apply,e.left_inv ex] using one)
    (fun v => by simpa only [Function.comp_apply,e.left_inv ex] using ort v)
  have at0 : d (z,0)=X p := by rw [eq]; simp [z,Function.comp_apply,e.left_inv ex]
  have yt : X p∈d.target := at0 ▸ d.map_source inside
  have back : d.symm (X p)=(z,0) := at0 ▸ d.left_inv inside
  let Ω := (e.target∩e.symm ⁻¹' U) ×ˢ ball (0:ℝ) r
  have op : IsOpen Ω := (e.symm.isOpen_inter_preimage uo).prod isOpen_ball
  have orig : (z,0)∈Ω := ⟨⟨et,by change e.symm (e p)∈U; rw [e.left_inv ex]; exact ku hp⟩,mem_ball_self rp⟩
  have near : ∀ᶠ y in 𝓝 (X p), d.symm y∈Ω := (d.symm.continuousAt yt).eventually (op.mem_nhds (back.symm ▸ orig))
  have germ : signed=ᶠ[𝓝 (X p)] Prod.snd ∘ d.symm := by
    filter_upwards [near,d.open_target.mem_nhds yt] with y hy ht
    let q : W := ⟨(e.symm (d.symm y).1,(d.symm y).2),hy.1.2,hy.2⟩
    have right : J q=y := by
      calc
        J q=d (d.symm y) := by rw [eq]; rfl
        _=y := d.right_inv ht
    exact (congrArg signed right.symm).trans (value q)
  have zero : signed (X p)=0 := by rw [germ.self_of_nhds]; change (d.symm (X p)).2=0; rw [back]
  have localSmooth : ContDiffAt ℝ 1 d.symm (X p) := by simpa only [Function.comp_apply,e.left_inv ex] using sm
  exact ⟨(contDiffAt_snd.comp _ localSmooth).congr_of_eventuallyEq germ,zero⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_regular_core_signed_tube
