import TwoAxisHelicoid.OriginalGenusOneCoreTube

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- Around a specified compact part of the original surface there is
an ambient open set whose normal-foot projection lands inside the
specified open core. Its Euclidean position is a C¹ map everywhere
on that open set. -/
theorem original_open_core_foot_retraction (s : OriginalSmoothHelicoid) {V K : Set s.carrier}
    (vo : IsOpen V) (kc : IsCompact K) (kn : K.Nonempty) (kv : K⊆V) :
    ∃ (O : Set SurfaceEuclideanSpace) (P : SurfaceEuclideanSpace → s.carrier),
      IsOpen O ∧ s.euclideanPosition '' K⊆O ∧ MapsTo P O V ∧ ContinuousOn P O ∧
      (∀ b∈K, P (s.euclideanPosition b)=b) ∧
      ∀ y∈O, ContDiffAt ℝ 1 (s.euclideanPosition ∘ P) y := by
  classical
  let X := s.euclideanPosition
  obtain ⟨N,_,_,_,S,charts⟩ := original_smooth_regular_normal_geometry s
  let _ := S
  have inj := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective.comp s.closedEmbedding.injective
  obtain ⟨U,r,uo,ku,rp,emb⟩ := compact_immersed_core_normal_tube kc inj.injOn (fun b _ => charts b)
  let W := U ×ˢ ball (0:ℝ) r
  let J := W.domRestrict (fun q : s.carrier × ℝ => X q.1+q.2 • N q.1)
  let H := emb.toIsEmbedding.toHomeomorph
  let d := kn.choose
  let P := fun y => if hy : y∈range J then (H.symm ⟨y,hy⟩).1.1 else d
  have value (q : W) : P (J q)=q.1.1 := by
    dsimp only [P]
    rw [dite_eq_left (mem_range_self q)]
    exact congrArg (fun t : W => t.1.1) (H.symm_apply_apply q)
  have cp : ContinuousOn P (range J) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have eq : (range J).domRestrict P=(fun t : W => t.1.1) ∘ H.symm := by
      funext q
      simp only [domRestrict_apply,P,dite_eq_left q.2,Function.comp_apply]
      rfl
    rw [eq]
    exact continuous_fst.comp (continuous_subtype_val.comp H.symm.continuous)
  have foot (b : s.carrier) (hb : b∈K) : X b∈range J ∧ P (X b)=b := by
    let q : W := ⟨(b,0),ku hb,mem_ball_self rp⟩
    have atq : J q=X b := by change X b+(0:ℝ) • N b=X b; simp
    exact ⟨⟨q,atq⟩,atq ▸ value q⟩
  have smooth (b : s.carrier) (hb : b∈K) : ContDiffAt ℝ 1 (X ∘ P) (X b) := by
    let a := chartAt ℂ b
    let z := a b
    have ab : b∈a.source := mem_chart_source ℂ b
    obtain ⟨sx,sn,im,unit,perp⟩ := charts b
    obtain ⟨e,inside,eq,sm⟩ := normal_coordinate_smooth_local_inverse (X := X ∘ a.symm) (N := N ∘ a.symm) (z := z)
      sx sn im (by simpa only [Function.comp_apply,z,a.left_inv ab] using unit)
      (fun v => by simpa only [Function.comp_apply,z,a.left_inv ab] using perp v)
    have at0 : e (z,0)=X b := by rw [eq]; simp [z,Function.comp_apply,a.left_inv ab]
    have yt : X b∈e.target := at0 ▸ e.map_source inside
    have back : e.symm (X b)=(z,0) := at0 ▸ e.left_inv inside
    let Ω := (a.target∩a.symm ⁻¹' U) ×ˢ ball (0:ℝ) r
    have op : IsOpen Ω := (a.symm.isOpen_inter_preimage uo).prod isOpen_ball
    have orig : (z,0)∈Ω := ⟨⟨a.map_source ab,by change a.symm (a b)∈U; rw [a.left_inv ab]; exact ku hb⟩,mem_ball_self rp⟩
    have near := (e.symm.continuousAt yt).eventually (op.mem_nhds (back.symm ▸ orig))
    have germ : P=ᶠ[𝓝 (X b)] a.symm ∘ Prod.fst ∘ e.symm := by
      filter_upwards [near,e.open_target.mem_nhds yt] with y hy ht
      let q : W := ⟨(a.symm (e.symm y).1,(e.symm y).2),hy.1.2,hy.2⟩
      have right : J q=y := (show J q=e (e.symm y) by rw [eq]; rfl).trans (e.right_inv ht)
      exact (congrArg P right.symm).trans (value q)
    have sinv : ContDiffAt ℝ 1 e.symm (X b) := by simpa only [Function.comp_apply,z,a.left_inv ab] using sm
    have sfoot : ContDiffAt ℝ 1 (X ∘ a.symm) (e.symm (X b)).1 := back.symm ▸ sx
    exact (sfoot.comp (X b) (contDiffAt_fst.comp (X b) sinv)).congr_of_eventuallyEq (germ.fun_comp X)
  let O := interior {y | y∈range J ∧ P y∈V ∧ ContDiffAt ℝ 1 (X ∘ P) y}
  have member {y} (hy : y∈O) := interior_subset hy
  refine ⟨O,P,isOpen_interior,?_,fun _ h => (member h).2.1,cp.mono (fun _ h => (member h).1),
    fun b hb => (foot b hb).2,fun _ h => (member h).2.2⟩
  rintro y ⟨b,hb,rfl⟩
  obtain ⟨hit,fix⟩ := foot b hb
  have openImg : IsOpen (range J) := emb.isOpen_range
  have into := (cp.continuousAt (openImg.mem_nhds hit)).eventually (vo.mem_nhds (fix.symm ▸ kv hb))
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [openImg.mem_nhds hit,into,(smooth b hb).eventually (by simp)] with z h v r
  exact ⟨h,v,r⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_open_core_foot_retraction
