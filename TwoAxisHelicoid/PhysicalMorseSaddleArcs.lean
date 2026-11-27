import TwoAxisHelicoid.MorseSaddleHyperbolaArcs
import TwoAxisHelicoid.MorseHeightLevelGerms

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology

/-- A product germ in an actual surface chart controls an entire closed
coordinate square about the saddle. -/
theorem saddle_height_closed_coordinate_square {M : Type*} [TopologicalSpace M]
    {h : M → ℝ} {p : M} (e : OpenPartialHomeomorph M (ℝ×ℝ))
    (src : p∈e.source) (center : e p=0) (model : ∀ᶠ x in 𝓝 p, h x=h p+(e x).1*(e x).2) :
    ∃ r : ℝ, 0<r ∧ ∀ w : ℝ×ℝ, |w.1|≤r → |w.2|≤r →
      w∈e.target ∧ h (e.symm w)=h p+w.1*w.2 := by
  have ht : (0:ℝ×ℝ)∈e.target := center ▸ e.map_source src
  have ip : e.symm 0=p := by rw [← center,e.left_inv src]
  have pull := (show Tendsto e.symm (𝓝 0) (𝓝 p) from ip ▸ e.continuousAt_symm ht).eventually model
  have good : ∀ᶠ w in 𝓝 (0:ℝ×ℝ), w∈e.target ∧ h (e.symm w)=h p+w.1*w.2 := by
    filter_upwards [e.open_target.mem_nhds ht,pull] with w hw eq
    exact ⟨hw,by simpa only [e.right_inv hw] using eq⟩
  obtain ⟨b,bp,near⟩ := Metric.mem_nhds_iff.mp good
  refine ⟨b/2,half_pos bp,?_⟩
  intro w hw hv
  apply near
  change max (dist w.1 0) (dist w.2 0)<b
  simpa only [Real.dist_eq,sub_zero] using max_lt (hw.trans_lt (half_lt_self bp)) (hv.trans_lt (half_lt_self bp))

/-- In each of the four signed quadrants of a Morse saddle, regular
height arcs continuously degenerate to the two corresponding radial
segments. Their endpoints stay on the same two sides of the square in
the physical surface chart. -/
theorem saddle_height_arc_homotopies {M : Type*} [TopologicalSpace M]
    {h : M → ℝ} {p : M} (e : OpenPartialHomeomorph M (ℝ×ℝ))
    (src : p∈e.source) (center : e p=0) (model : ∀ᶠ x in 𝓝 p, h x=h p+(e x).1*(e x).2) :
    ∃ r : ℝ, 0<r ∧ ∀ a b : ℝ, |a|=1 → |b|=1 →
      ∃ F : ℝ×ℝ → M, ContinuousOn F (Icc 0 (r^2/2) ×ˢ Icc (-1) 1) ∧
        (∀ s∈Icc (0:ℝ) (r^2/2), ∀ t∈Icc (-1:ℝ) 1, F (s,t)∈e.source ∧ h (F (s,t))=h p+a*b*s) ∧
        (∀ s∈Icc (0:ℝ) (r^2/2), e (F (s,-1))=(a*(s/r),b*r) ∧ e (F (s,1))=(a*r,b*(s/r))) ∧
        ∀ s∈Icc (0:ℝ) (r^2/2), InjOn (fun t => F (s,t)) (Icc (-1:ℝ) 1) := by
  obtain ⟨r,rp,square⟩ := saddle_height_closed_coordinate_square e src center model
  refine ⟨r,rp,?_⟩
  intro a b aa bb
  let A := fun q : ℝ×ℝ => saddleSquareArc r q.1 q.2
  let B := fun q : ℝ×ℝ => (a*(A q).1,b*(A q).2)
  let T := Icc 0 (r^2/2) ×ˢ Icc (-1:ℝ) 1
  have small {s : ℝ} (hs : s∈Icc 0 (r^2/2)) : s<r^2 := hs.2.trans_lt (half_lt_self (sq_pos_of_pos rp))
  have boxes {q : ℝ×ℝ} (hq : q∈T) : (A q).1∈Icc 0 r ∧ (A q).2∈Icc 0 r ∧ (A q).1*(A q).2=q.1 := by
    have mem : A q∈saddleSquareArc r q.1 '' Icc (-1:ℝ) 1 := ⟨q.2,hq.2,rfl⟩
    rw [saddleSquareArc_image rp hq.1.1 (small hq.1)] at mem
    exact mem
  have inChart {q : ℝ×ℝ} (hq : q∈T) : B q∈e.target ∧ h (e.symm (B q))=h p+(B q).1*(B q).2 := by
    obtain ⟨x,y,_⟩ := boxes hq
    apply square
    · simpa only [B,abs_mul,aa,one_mul,abs_of_nonneg x.1] using x.2
    · simpa only [B,abs_mul,bb,one_mul,abs_of_nonneg y.1] using y.2
  have cA : Continuous A := saddleSquareArc_continuous r
  have cB : Continuous B := (continuous_const.mul cA.fst).prodMk (continuous_const.mul cA.snd)
  have lo : (-1:ℝ)∈Icc (-1) 1 := by constructor <;> norm_num
  have hi : (1:ℝ)∈Icc (-1) 1 := by constructor <;> norm_num
  refine ⟨e.symm ∘ B,e.continuousOn_symm.comp cB.continuousOn (fun _ hq => (inChart hq).1),?_,?_,?_⟩
  · intro s hs t ht
    have hq : (s,t)∈T := ⟨hs,ht⟩
    obtain ⟨target,height⟩ := inChart hq
    refine ⟨e.map_target target,height.trans ?_⟩
    change h p+(a*(A (s,t)).1)*(b*(A (s,t)).2)=_
    calc
      _=h p+a*b*((A (s,t)).1*(A (s,t)).2) := by ring
      _=h p+a*b*s := by rw [(boxes hq).2.2]
  · intro s hs
    obtain ⟨l,u⟩ := saddleSquareArc_endpoints rp hs.1
    change e (e.symm (B (s,-1)))=_ ∧ e (e.symm (B (s,1)))=_
    rw [e.right_inv (inChart (q:=(s,-1)) ⟨hs,lo⟩).1,e.right_inv (inChart (q:=(s,1)) ⟨hs,hi⟩).1]
    simp only [B,A,l,u,and_self]
  · intro s hs t ht u hu equal
    have eq : B (s,t)=B (s,u) := e.symm.injOn (inChart (q:=(s,t)) ⟨hs,ht⟩).1 (inChart (q:=(s,u)) ⟨hs,hu⟩).1 equal
    have an : a≠0 := fun az => by simp [az] at aa
    have bn : b≠0 := fun bz => by simp [bz] at bb
    apply saddleSquareArc_injective rp hs.1 (small hs)
    exact Prod.ext (mul_left_cancel₀ an (congrArg Prod.fst eq)) (mul_left_cancel₀ bn (congrArg Prod.snd eq))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.saddle_height_arc_homotopies

