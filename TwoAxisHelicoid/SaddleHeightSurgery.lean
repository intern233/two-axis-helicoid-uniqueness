import TwoAxisHelicoid.SaddleReturnRadiusCuts
import TwoAxisHelicoid.RegularHeightPathDeformation
import TwoAxisHelicoid.PairedHeightPathDisplacement
import TwoAxisHelicoid.CountableTiltedCriticalValues

namespace TwoAxisHelicoid
open Complex Set Filter Topology Function
open scoped Topology unitInterval

/-- A nonconstant affine function on any right interval at zero takes
a value outside a countable exceptional set, while satisfying a given
neighborhood condition. -/
theorem affine_height_outside_countable_on_right {B : Set ℝ} (count : B.Countable)
    (c k : ℝ) (kn : k≠0) {R : ℝ} (rp : 0<R) {P : ℝ → Prop}
    (near : ∀ᶠ s in 𝓝 (0:ℝ), P s) : ∃ s∈Ioo 0 R, c+k*s∉B ∧ P s := by
  obtain ⟨d,dp,all⟩ := height_shift_interval_of_eventually near
  let f := fun s : ℝ => c+k*s
  have inj : Injective f := fun _ _ eq => mul_left_cancel₀ kn (add_left_cancel eq)
  have pos : 0<min d R := lt_min dp rp
  obtain ⟨s,good,hs⟩ := ((count.preimage inj).dense_compl ℝ).exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr pos)
  exact ⟨s,⟨hs.1,hs.2.trans_le (min_le_right _ _)⟩,good,
    all s ⟨(neg_nonpos.mpr dp.le).trans hs.1.le,hs.2.le.trans (min_le_left _ _)⟩⟩

/-- Move the regular middle path, matching both endpoints of the
given saddle smoothing. Unequal base displacements force a marked
obstruction at true nearby heights outside any countable set. -/
theorem regular_path_paired_smoothing {L : PeriodPair} (H : PeriodTorus L ≃ₜ Circle×Circle)
    (marked : ∀ z, H (periodTorusProjection L z)=planeCircleCoordinates L z)
    {h : PeriodTorus L → ℝ} (A B : C(I,ℂ)) (Q : C(ℝ×I,PeriodTorus L)) (v : C(ℝ,ℝ))
    {c k R : ℝ} (rp : 0<R) (kn : k≠0) (affine : ∀ s∈Icc (0:ℝ) R, v s=c+k*s)
    (middle : ∀ t, let y := periodTorusProjection L (A t)
      h y=v 0 ∧ ∃ e : OpenPartialHomeomorph (PeriodTorus L) (ℝ×ℝ), y∈e.source ∧ ∀ w∈e.target, h (e.symm w)=w.2)
    (level : ∀ s t, h (Q (s,t))=v s) (liftB : ∀ t, periodTorusProjection L (B t)=Q (0,t))
    (start : Q (0,0)=periodTorusProjection L (A 0)) (finish : Q (0,1)=periodTorusProjection L (A 1))
    (different : A 1-A 0≠B 1-B 0) {E : Set ℝ} (count : E.Countable) :
    ∃ u∉E, ∃ x : h ⁻¹' {u}, ¬∃ a b : C(connectedComponent x,ℝ), ∀ q : connectedComponent x,
      normalizedPhase (a q)=(H q.1.1).1 ∧ normalizedPhase (b q)=(H q.1.1).2 := by
  let δ : C(I,PeriodTorus L) := ⟨fun t => periodTorusProjection L (A t),QuotientAddGroup.continuous_mk.comp A.continuous⟩
  let ending := fun t : I => (⟨fun s => Q (s,t),Q.continuous.comp (continuous_id.prodMk continuous_const)⟩ : C(ℝ,PeriodTorus L))
  obtain ⟨d,dp,F,cf,base,each⟩ := regular_height_path_deformation δ v (fun t => (middle t).1)
    (fun t => (middle t).2) (ending 0) (ending 1) start finish (.of_forall fun s => level s 0) (.of_forall fun s => level s 1)
  have ord : -d≤d := by linarith
  let j := fun s : ℝ => (projIcc (-d) d ord s : ℝ)
  have cj : Continuous j := continuous_subtype_val.comp continuous_projIcc
  have inside (s : ℝ) : j s∈Icc (-d) d := (projIcc (-d) d ord s).2
  have fix {s : ℝ} (hs : s∈Icc (-d) d) : j s=s := congrArg Subtype.val (projIcc_of_mem ord hs)
  have j0 : j 0=0 := fix ⟨neg_nonpos.mpr dp.le,dp.le⟩
  let K : C(ℝ×I,ℝ×I) := ⟨fun q => (j q.1,q.2),(cj.comp continuous_fst).prodMk continuous_snd⟩
  let P : C(ℝ×I,PeriodTorus L) := ⟨F ∘ K,cf.comp_continuous K.continuous (fun q => ⟨inside q.1,mem_univ _⟩)⟩
  have found := nearby_obstructed_height_from_paired_paths L H marked P (Q.comp K) (h:=h) (v:=fun s => v (j s))
    (fun s t => ⟨(each (j s) (inside s)).1 t,level (j s) t⟩)
    (fun s => (each (j s) (inside s)).2.1) (fun s => (each (j s) (inside s)).2.2) 0 A B
    (fun t => by change δ t=F (j 0,t); rw [j0,base])
    (fun t => by change periodTorusProjection L (B t)=Q (j 0,t); rw [j0,liftB]) different
  have st : 0<min R d := lt_min rp dp
  obtain ⟨s,hs,ok,occ⟩ := affine_height_outside_countable_on_right count c k kn st found
  have sr : s∈Icc 0 R := ⟨hs.1.le,hs.2.le.trans (min_le_left _ _)⟩
  have sd : s∈Icc (-d) d := ⟨(neg_nonpos.mpr dp.le).trans hs.1.le,hs.2.le.trans (min_le_right _ _)⟩
  exact ⟨c+k*s,ok,by rwa [fix sd,affine s sr] at occ⟩

/-- Resolving the two adjacent arms of a nontrivially lifted saddle
return produces a marked nonlifting component outside any countable
set of actual heights. -/
theorem saddle_return_has_nonlifting_height_outside_countable {L : PeriodPair}
    (H : PeriodTorus L ≃ₜ Circle×Circle) (marked : ∀ z, H (periodTorusProjection L z)=planeCircleCoordinates L z)
    {h : PeriodTorus L → ℝ} (ret : HasSeparatedSaddleReturn L h) {E : Set ℝ} (count : E.Countable) :
    ∃ u∉E, ∃ x : h ⁻¹' {u}, ¬∃ a b : C(connectedComponent x,ℝ), ∀ q : connectedComponent x,
      normalizedPhase (a q)=(H q.1.1).1 ∧ normalizedPhase (b q)=(H q.1.1).2 := by
  obtain ⟨p,e,γ,a,b,src,center,model,cγ,ap,bp,apart,al,bl,reg,vert,horiz⟩ := oriented_saddle_return ret
  let π := periodTorusProjection L
  obtain ⟨d,ds,repr⟩ := periodTorusProjection_isLocalHomeomorph L a
  have atP : p=d a := ap.symm.trans (congrFun repr a)
  have pt : p∈d.target := atP.symm ▸ d.map_source ds
  obtain ⟨R,Rp,square⟩ := saddle_closed_square_in_neighborhood e src center model (d.open_target.mem_nhds pt)
  obtain ⟨D,Dp,cuts⟩ := saddle_return_equal_radius_cuts γ e src center cγ ap bp al bl (fun t => (reg t).2.1)
    vert horiz d ds repr
  let r := min R D/2
  have pos : 0<min R D := lt_min Rp Dp
  have rp : 0<r := half_pos pos
  have rd : r<D := (half_lt_self pos).trans_le (min_le_right _ _)
  have rr : r≤R := (half_le_self pos.le).trans (min_le_left _ _)
  obtain ⟨t₁,t₂,u,v,uu,vv,⟨ins₁,tip₁,sec₁⟩,ins₂,tip₂,sec₂⟩ := cuts r ⟨rp,rd⟩
  obtain ⟨Q,V,V0,aff,each,Q0,Q1⟩ := signed_saddle_square_path (h:=h) e rp uu vv
    (fun w x y => square w (x.trans rr) (y.trans rr))
  let interp := fun t : I => (1-(t:ℝ))*t₁+(t:ℝ)*t₂
  have ci : Continuous interp := ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.mul continuous_const)
  let A : C(I,ℂ) := ⟨γ ∘ interp,cγ.comp ci⟩
  have A0 : A 0=γ t₁ := by simp [A,interp]
  have A1 : A 1=γ t₂ := by simp [A,interp]
  have start : Q (0,0)=π (A 0) := by rw [Q0,A0,← tip₁,e.left_inv ins₁]
  have finish : Q (0,1)=π (A 1) := by rw [Q1,A1,← tip₂,e.left_inv ins₂]
  let B : C(I,ℂ) := ⟨fun t => d.symm (Q (0,t)),d.continuousOn_symm.comp_continuous
    (Q.continuous.comp (continuous_const.prodMk continuous_id)) (fun t => (each 0 t).1)⟩
  have liftB (t : I) : π (B t)=Q (0,t) := (congrFun repr _).trans (d.right_inv (each 0 t).1)
  have B0 : B 0=A 0 := by change d.symm (Q (0,0))=_; rw [start,A0]; exact sec₁
  have B1 : B 1=A 1-(b-a) := by change d.symm (Q (0,1))=_; rw [finish,A1]; exact sec₂
  have different : A 1-A 0≠B 1-B 0 := by
    intro eq
    rw [B0,B1] at eq
    apply apart
    linear_combination -eq
  have un : u≠0 := fun eq => by simp [eq] at uu
  have vn : v≠0 := fun eq => by simp [eq] at vv
  apply regular_path_paired_smoothing H marked A B Q V (half_pos (sq_pos_of_pos rp))
    (mul_ne_zero un vn) aff _ (fun s t => (each s t).2) liftB start finish different count
  intro t
  exact ⟨(reg (interp t)).1.trans V0.symm,(reg (interp t)).2.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.saddle_return_has_nonlifting_height_outside_countable
