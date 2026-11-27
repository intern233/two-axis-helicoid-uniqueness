import TwoAxisHelicoid.ChartHeightPathTransport
import TwoAxisHelicoid.HeightPathSegments
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.Linarith

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped Topology unitInterval

theorem height_shift_interval_of_eventually {p : ℝ → Prop} (near : ∀ᶠ s in 𝓝 (0:ℝ), p s) :
    ∃ d : ℝ, 0<d ∧ ∀ s∈Icc (-d) d, p s := by
  obtain ⟨b,bp,sub⟩ := Metric.mem_nhds_iff.mp near
  refine ⟨b/2,half_pos bp,?_⟩
  intro s hs
  apply sub
  rw [Metric.mem_ball,Real.dist_eq,sub_zero]
  exact (abs_le.mpr hs).trans_lt (half_lt_self bp)

/-- Transport a regular segment on its actual height levels with
prescribed sections at both physical endpoints. The choice of section
at a subdivision vertex is shared by the segments on its two sides. -/
theorem regular_height_chart_segment_deformation {M : Type*} [TopologicalSpace M]
    {h : M → ℝ} (e : OpenPartialHomeomorph M (ℝ×ℝ))
    (height : ∀ w∈e.target, h (e.symm w)=w.2)
    (γ : C(I,M)) (v : C(ℝ,ℝ)) (P : I → C(ℝ,M))
    (p0 : ∀ t, P t 0=γ t) (pv : ∀ t, ∀ᶠ s in 𝓝 (0:ℝ), h (P t s)=v s)
    {l r : I} (order : l≤r) (inside : ∀ t∈Icc l r, γ t∈e.source)
    (level : ∀ t∈Icc l r, h (γ t)=v 0) :
    HeightPathDeformationOn h v γ (fun t s => P t s) l r := by
  rcases order.eq_or_lt with same|strict
  · subst r
    obtain ⟨d,dp,good⟩ := height_shift_interval_of_eventually (pv l)
    refine ⟨d,dp,fun q => P l q.1,((P l).continuous.comp continuous_fst).continuousOn,?_,?_⟩
    · intro t ht
      have eq := le_antisymm ht.2 ht.1
      exact (p0 l).trans (congrArg γ eq.symm)
    · exact fun s hs => ⟨fun _ _ => good s hs,rfl,rfl⟩
  have lmem : l∈Icc l r := ⟨le_rfl,order⟩
  have rmem : r∈Icc l r := ⟨order,le_rfl⟩
  have localSource (t : I) (ht : t∈Icc l r) :
      ∀ᶠ s in 𝓝 (0:ℝ), P t s∈e.source := (P t).continuous.continuousAt.eventually
        (e.open_source.mem_nhds (by rw [p0]; exact inside t ht))
  have near : ∀ᶠ s in 𝓝 (0:ℝ), (P l s∈e.source ∧ h (P l s)=v s) ∧
      (P r s∈e.source ∧ h (P r s)=v s) :=
    ((localSource l lmem).and (pv l)).and ((localSource r rmem).and (pv r))
  obtain ⟨a,ap,good⟩ := height_shift_interval_of_eventually near
  have orderA : -a≤a := by linarith
  let clamp := fun s : ℝ => (projIcc (-a) a orderA s : ℝ)
  have cc : Continuous clamp := continuous_subtype_val.comp continuous_projIcc
  have clamped (s : ℝ) : clamp s∈Icc (-a) a := (projIcc (-a) a orderA s).2
  have fixed (s : ℝ) (hs : s∈Icc (-a) a) : clamp s=s :=
    congrArg Subtype.val (projIcc_of_mem orderA hs)
  let L : C(ℝ,ℝ) := ⟨fun s => (e (P l (clamp s))).1,continuous_fst.comp
    (e.continuousOn.comp_continuous ((P l).continuous.comp cc) (fun s => (good _ (clamped s)).1.1))⟩
  let R : C(ℝ,ℝ) := ⟨fun s => (e (P r (clamp s))).1,continuous_fst.comp
    (e.continuousOn.comp_continuous ((P r).continuous.comp cc) (fun s => (good _ (clamped s)).2.1))⟩
  let T := Icc l r
  let tL : T := ⟨l,lmem⟩
  let tR : T := ⟨r,rmem⟩
  let blend : C(T,ℝ) := ⟨fun t => (((t.1:ℝ))-(l:ℝ))/((r:ℝ)-(l:ℝ)),
    ((continuous_subtype_val.comp continuous_subtype_val).sub continuous_const).div_const _⟩
  have bL : blend tL=0 := by change ((l:ℝ)-l)/_=0; rw [sub_self,zero_div]
  have bR : blend tR=1 := div_self (sub_ne_zero.mpr (ne_of_gt (show (l:ℝ)<r from strict)))
  have zeroA : (0:ℝ)∈Icc (-a) a := ⟨neg_nonpos.mpr ap.le,ap.le⟩
  let arc : C(T,M) := ⟨fun t => γ t.1,γ.continuous.comp continuous_subtype_val⟩
  obtain ⟨V,op,mem,F,cont,base,each⟩ := compact_height_chart_transport blend bL bR e height arc
    (fun t => inside _ t.2) (fun t => level _ t.2) v L R rfl
    (by change (e (P l (clamp 0))).1=(e (γ l)).1; rw [fixed _ zeroA,p0])
    (by change (e (P r (clamp 0))).1=(e (γ r)).1; rw [fixed _ zeroA,p0])
  obtain ⟨b,bp,vIn⟩ := height_shift_interval_of_eventually (op.mem_nhds mem)
  let d := min a b
  have sA : Icc (-d) d⊆Icc (-a) a := Icc_subset_Icc (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have sB : Icc (-d) d⊆Icc (-b) b := Icc_subset_Icc (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  let J := fun q : ℝ×I => (q.1,projIcc l r order q.2)
  have cj : Continuous J := continuous_fst.prodMk (continuous_projIcc.comp continuous_snd)
  refine ⟨d,lt_min ap bp,F ∘ J,cont.comp cj.continuousOn (fun _ hq => ⟨vIn _ (sB hq.1),trivial⟩),?_,?_⟩
  · intro t ht
    change F (0,projIcc l r order t)=γ t
    rw [projIcc_of_mem order ht]
    exact base ⟨t,ht⟩
  · intro s hs
    obtain ⟨all,left,right⟩ := each s (vIn _ (sB hs))
    have ats (t : I) (src : P t s∈e.source) (value : h (P t s)=v s) :
        e.symm ((e (P t s)).1,v s)=P t s := by
      have y := height (e (P t s)) (e.map_source src)
      rw [e.left_inv src,value] at y
      rw [y]
      exact e.left_inv src
    obtain ⟨⟨il,hl⟩,⟨ir,hr⟩⟩ := good s (sA hs)
    refine ⟨fun t _ => (all (projIcc l r order t)).2,?_,?_⟩
    · change F (s,projIcc l r order l)=P l s
      rw [projIcc_of_mem order lmem,left]
      change e.symm ((e (P l (clamp s))).1,v s)=P l s
      rw [fixed s (sA hs)]
      exact ats l il hl
    · change F (s,projIcc l r order r)=P r s
      rw [projIcc_of_mem order rmem,right]
      change e.symm ((e (P r (clamp s))).1,v s)=P r s
      rw [fixed s (sA hs)]
      exact ats r ir hr

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_height_chart_segment_deformation
