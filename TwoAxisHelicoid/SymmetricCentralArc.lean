import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

namespace TwoAxisHelicoid
open Set
/-- A planar arc reflected about the vertical line through its middle
point is simple precisely when its first half is simple and stays in
the indicated open half-plane. The orientation is fixed by one point. -/
theorem symmetric_central_arc_embedding_test {t : ℝ} (ht : 0<t) (f : ℝ → ℝ × ℝ)
    (cont : ContinuousOn (fun y => (f y).1) (Ioo 0 t))
    (sym : ∀ y∈Ioo 0 t, f (t-y)=(-(f y).1,(f y).2))
    (orientation : ∃ u∈Ioo 0 (t/2), 0<(f u).1) :
    (InjOn f (Ioo 0 t) ∧ ∀ y∈Ioo 0 t, 0<(f y).2) ↔
      InjOn f (Ioc 0 (t/2)) ∧ (∀ y∈Ioo 0 (t/2), 0<(f y).1) ∧ ∀ y∈Ioc 0 (t/2), 0<(f y).2 := by
  have sub : Ioc 0 (t/2)⊆Ioo 0 t := fun y hy => ⟨hy.1,by linarith [hy.2]⟩
  have op : Ioo 0 (t/2)⊆Ioc 0 (t/2) := fun _ hy => ⟨hy.1,hy.2.le⟩
  have mid : t/2∈Ioo 0 t := ⟨by linarith,by linarith⟩
  have center := congrArg Prod.fst (sym _ mid)
  rw [show t-t/2=t/2 by ring] at center
  change (f (t/2)).1= -(f (t/2)).1 at center
  have flip {y : ℝ} (hy : y∈Ioo 0 t) : t-y∈Ioo 0 t := ⟨by linarith [hy.2],by linarith [hy.1]⟩
  constructor
  · rintro ⟨simple,above⟩
    refine ⟨simple.mono sub,?_,fun y hy => above y (sub hy)⟩
    intro y hy
    obtain ⟨u,hu,pos⟩ := orientation
    by_contra! bad
    obtain ⟨s,hs,e⟩ := isPreconnected_Ioo.intermediate_value hy hu (cont.mono (op.trans sub))
      (show (0:ℝ)∈Icc (f y).1 (f u).1 from ⟨bad,pos.le⟩)
    change (f s).1=0 at e
    have full := sub (op hs)
    have same : f (t-s)=f s := (sym s full).trans (Prod.ext (by change -(f s).1=(f s).1; rw [e,neg_zero]) rfl)
    have middle := simple (flip full) full same
    linarith [hs.2]
  · rintro ⟨simple,side,above⟩
    have low {u : ℝ} (hu : u∈Ioc 0 (t/2)) : 0≤(f u).1 := by
      rcases hu.2.eq_or_lt with e|lt
      · rw [e]; linarith
      · exact (side _ ⟨hu.1,lt⟩).le
    have upper {v : ℝ} (hv : v∈Ioo 0 t) (h : t/2<v) : (f v).1<0 := by
      have p := side (t-v) ⟨by linarith [hv.2],by linarith⟩
      have e := congrArg Prod.fst (sym v hv)
      change (f (t-v)).1= -(f v).1 at e
      linarith
    refine ⟨?_,?_⟩
    · intro u hu v hv eq
      by_cases a : u≤t/2
      · by_cases b : v≤t/2
        · exact simple ⟨hu.1,a⟩ ⟨hv.1,b⟩ eq
        · exact ((upper hv (lt_of_not_ge b)).not_ge ((congrArg Prod.fst eq) ▸ low ⟨hu.1,a⟩)).elim
      · by_cases b : v≤t/2
        · exact ((upper hu (lt_of_not_ge a)).not_ge ((congrArg Prod.fst eq).symm ▸ low ⟨hv.1,b⟩)).elim
        · have reflected : f (t-u)=f (t-v) := (sym u hu).trans (by rw [eq]; exact (sym v hv).symm)
          have p := simple (x₁:=t-u) (x₂:=t-v) ⟨by linarith [hu.2],by linarith⟩ ⟨by linarith [hv.2],by linarith⟩ reflected
          linarith
    · intro y hy
      rcases le_or_gt y (t/2) with lower|high
      · exact above y ⟨hy.1,lower⟩
      · have e := congrArg Prod.snd (sym y hy)
        change (f (t-y)).2=(f y).2 at e
        exact (above (t-y) ⟨by linarith [hy.2],by linarith⟩).trans_eq e

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.symmetric_central_arc_embedding_test
