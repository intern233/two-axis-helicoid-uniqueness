import TwoAxisHelicoid.ActualQuarterHeightSlices
import Mathlib.Topology.Homeomorph.Lemmas

namespace TwoAxisHelicoid
open Set Topology

/-- A continuous family of strictly increasing functions on a compact
interval has continuous roots even when a root hits an endpoint. -/
theorem rectangle_closed_row_graph {L R u v s : ℝ} (lr : L≤R) {F : ℝ × ℝ → ℝ}
    (c : ContinuousOn F (Icc L R ×ˢ Icc u v))
    (row : ∀ y∈Icc u v, StrictMonoOn (fun x => F (x,y)) (Icc L R))
    (edges : ∀ y∈Icc u v, F (L,y)≤s ∧ s≤F (R,y)) :
    ∃ r : ℝ → ℝ, ContinuousOn r (Icc u v) ∧ ∀ y∈Icc u v, r y∈Icc L R ∧ F (r y,y)=s := by
  classical
  let C := Icc L R
  let J := Icc u v
  let P := C ×ˢ J
  let E : P → ℝ × ℝ := fun z => (F z.1,z.1.2)
  let _ : CompactSpace P := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  have ec : Continuous E := (continuousOn_iff_continuous_domRestrict.mp c).prodMk (continuous_snd.comp continuous_subtype_val)
  have ei : Function.Injective E := by
    intro a b e
    have h := congrArg Prod.snd e
    have k := congrArg Prod.fst e
    change a.1.2=b.1.2 at h
    change F (a.1.1,a.1.2)=F (b.1.1,b.1.2) at k
    rw [← h] at k
    exact Subtype.ext (Prod.ext ((row _ a.2.2).injOn a.2.1 b.2.1 k) h)
  have one (y : ℝ) (hy : y∈J) : ∃ x∈C, F (x,y)=s := by
    have cy : ContinuousOn (fun x => F (x,y)) C := c.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hx => ⟨hx,hy⟩)
    exact intermediate_value_Icc lr cy (edges y hy)
  let r := fun y => if hy : y∈J then (one y hy).choose else 0
  have prop (y : ℝ) (hy : y∈J) : r y∈C ∧ F (r y,y)=s := by
    simpa only [r,dite_eq_left hy] using (one y hy).choose_spec
  let lift : J → P := fun y => ⟨(r y.1,y.1),(prop y.1 y.2).1,y.2⟩
  have comp : E ∘ lift=fun y : J => (s,y.1) := funext fun y => Prod.ext (prop _ y.2).2 rfl
  have continuous_lift : Continuous lift := (ec.isClosedEmbedding ei).isEmbedding.isInducing.continuous_iff.mpr (by
    rw [comp]
    exact continuous_const.prodMk continuous_subtype_val)
  exact ⟨r,continuousOn_iff_continuous_domRestrict.mpr (continuous_fst.comp (continuous_subtype_val.comp continuous_lift)),prop⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangle_closed_row_graph
