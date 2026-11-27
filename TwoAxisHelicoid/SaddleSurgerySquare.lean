import TwoAxisHelicoid.MorseSaddleHyperbolaArcs
import TwoAxisHelicoid.MorseHeightLevelGerms
import Mathlib.Topology.UnitInterval

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology unitInterval
set_option maxHeartbeats 1600000

/-- A physical Morse product chart contains a closed coordinate square
on which the height formula holds and whose inverse lies in any given
neighborhood of the saddle, in particular an evenly covered one. -/
theorem saddle_closed_square_in_neighborhood {M : Type*} [TopologicalSpace M]
    {h : M → ℝ} {p : M} (e : OpenPartialHomeomorph M (ℝ×ℝ))
    (src : p∈e.source) (center : e p=0)
    (model : ∀ᶠ x in 𝓝 p, h x=h p+(e x).1*(e x).2)
    {U : Set M} (nbhd : U∈𝓝 p) :
    ∃ R : ℝ, 0<R ∧ ∀ w : ℝ×ℝ, |w.1|≤R → |w.2|≤R →
      w∈e.target ∧ e.symm w∈U ∧ h (e.symm w)=h p+w.1*w.2 := by
  have ht : (0:ℝ×ℝ)∈e.target := center ▸ e.map_source src
  have ip : e.symm 0=p := by rw [← center,e.left_inv src]
  have pull : Tendsto e.symm (𝓝 0) (𝓝 p) := ip ▸ e.continuousAt_symm ht
  have good : ∀ᶠ w in 𝓝 (0:ℝ×ℝ),
      w∈e.target ∧ e.symm w∈U ∧ h (e.symm w)=h p+w.1*w.2 := by
    filter_upwards [e.open_target.mem_nhds ht,pull.eventually nbhd,pull.eventually model] with w hw hu eq
    exact ⟨hw,hu,by simpa only [e.right_inv hw] using eq⟩
  obtain ⟨b,bp,near⟩ := Metric.mem_nhds_iff.mp good
  refine ⟨b/2,half_pos bp,?_⟩
  intro w hw hv
  apply near
  change max (dist w.1 0) (dist w.2 0)<b
  simpa only [Real.dist_eq,sub_zero] using max_lt (hw.trans_lt (half_lt_self bp)) (hv.trans_lt (half_lt_self bp))

/-- At a prescribed radius, the signed hyperbolas give a continuous
second path on the same physical height, even through the saddle at
parameter zero. All paths stay in the prescribed covering chart. -/
theorem signed_saddle_square_path {M : Type*} [TopologicalSpace M]
    {h : M → ℝ} {c : ℝ} {U : Set M} (e : OpenPartialHomeomorph M (ℝ×ℝ))
    {r a b : ℝ} (rp : 0<r) (aa : |a|=1) (bb : |b|=1)
    (square : ∀ w : ℝ×ℝ, |w.1|≤r → |w.2|≤r →
      w∈e.target ∧ e.symm w∈U ∧ h (e.symm w)=c+w.1*w.2) :
    ∃ (Q : C(ℝ×I,M)) (v : C(ℝ,ℝ)), v 0=c ∧
      (∀ s∈Icc (0:ℝ) (r^2/2), v s=c+a*b*s) ∧
      (∀ s t, Q (s,t)∈U ∧ h (Q (s,t))=v s) ∧
      Q (0,0)=e.symm (0,b*r) ∧ Q (0,1)=e.symm (a*r,0) := by
  let top := r^2/2
  have tp : 0<top := half_pos (sq_pos_of_pos rp)
  let k := fun s : ℝ => (projIcc 0 top tp.le s : ℝ)
  have ck : Continuous k := continuous_subtype_val.comp continuous_projIcc
  have kin (s : ℝ) : k s∈Icc 0 top := (projIcc 0 top tp.le s).2
  have kfix {s : ℝ} (hs : s∈Icc 0 top) : k s=s := congrArg Subtype.val (projIcc_of_mem tp.le hs)
  have k0 : k 0=0 := kfix ⟨le_rfl,tp.le⟩
  let V : C(ℝ,ℝ) := ⟨fun s => c+a*b*k s,continuous_const.add (continuous_const.mul ck)⟩
  let A := fun q : ℝ×I => saddleSquareArc r (k q.1) (2*(q.2:ℝ)-1)
  have cA : Continuous A := (saddleSquareArc_continuous r).comp
    ((ck.comp continuous_fst).prodMk
      ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub continuous_const))
  let B := fun q : ℝ×I => (a*(A q).1,b*(A q).2)
  have cB : Continuous B := (continuous_const.mul cA.fst).prodMk (continuous_const.mul cA.snd)
  have actual (q : ℝ×I) : (A q).1∈Icc 0 r ∧ (A q).2∈Icc 0 r ∧ (A q).1*(A q).2=k q.1 := by
    have mem : A q∈saddleSquareArc r (k q.1) '' Icc (-1:ℝ) 1 :=
      ⟨2*(q.2:ℝ)-1,⟨by linarith [q.2.2.1],by linarith [q.2.2.2]⟩,rfl⟩
    rw [saddleSquareArc_image rp (kin _).1 ((kin _).2.trans_lt (half_lt_self (sq_pos_of_pos rp)))] at mem
    exact mem
  have good (q : ℝ×I) : B q∈e.target ∧ e.symm (B q)∈U ∧ h (e.symm (B q))=c+(B q).1*(B q).2 := by
    obtain ⟨x,y,_⟩ := actual q
    apply square
    · simpa only [B,abs_mul,aa,one_mul,abs_of_nonneg x.1] using x.2
    · simpa only [B,abs_mul,bb,one_mul,abs_of_nonneg y.1] using y.2
  let Q : C(ℝ×I,M) := ⟨e.symm ∘ B,e.continuousOn_symm.comp_continuous cB (fun q => (good q).1)⟩
  refine ⟨Q,V,by simp [V,k0],fun s hs => by simp [V,kfix hs],?_,?_,?_⟩
  · intro s t
    refine ⟨(good (s,t)).2.1,(good (s,t)).2.2.trans ?_⟩
    change c+(a*(A (s,t)).1)*(b*(A (s,t)).2)=c+a*b*k s
    linear_combination a*b*(actual (s,t)).2.2
  · have l := (saddleSquareArc_endpoints (s:=0) rp le_rfl).1
    simp [Q,Function.comp_def,B,A,k0,l]
  · have u := (saddleSquareArc_endpoints (s:=0) rp le_rfl).2
    simp [Q,Function.comp_def,B,A,k0,show (2:ℝ)-1=1 by norm_num,u]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.saddle_closed_square_in_neighborhood
#print axioms TwoAxisHelicoid.signed_saddle_square_path
