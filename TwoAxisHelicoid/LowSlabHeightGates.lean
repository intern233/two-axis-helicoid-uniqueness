import TwoAxisHelicoid.CertifiedQuarterHeightRows
import TwoAxisHelicoid.LowSlabEdgeSound

namespace TwoAxisHelicoid
open Complex Set

/-- The three row gates bound low positive levels in the intermediate
rectangle and at the early cutoff. The vertical-axis crossing precedes
the cutoff strictly for every one of those levels. -/
theorem low_slab_height_gates
    (gate : CheckedLowSlabEdge (.height true (1/4)) true (11/16) (7/32) (7/16))
    (left : CheckedLowSlabEdge (.height false 0) true (15/32) (3/8) (1/2))
    (right : CheckedLowSlabEdge (.height true (1/4)) true (3/5) (3/8) (1/2))
    (early : CheckedLowSlabEdge (.height false 0) true (9/16) (7/32) (7/32)) :
    let p := certifiedClosedParameters
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    (1/4<(H ⟨1,7/32⟩).re) ∧
    (∀ x∈Icc (0:ℝ) 1, 0<(H ⟨x,7/32⟩).re → 9/16<x) ∧
    (∀ x∈Icc (0:ℝ) 1, ∀ y∈Icc (3/8:ℝ) (1/2), (H ⟨x,y⟩).re∈Ioc (0:ℝ) (1/4) → x∈Icc (15/32:ℝ) (3/5)) ∧
    ∀ x∈Icc (0:ℝ) 1, ∀ y∈Ioc (0:ℝ) (7/32), 0<(H ⟨x,y⟩).re → 1/2≤x := by
  intro p H
  have tl := (by norm_num [rootTLower] : (43/50:ℝ)<rootTLower).trans certifiedClosedParameters_bounds.1.1
  obtain ⟨rows,zero⟩ := certified_quarter_height_row_order
  have yy : (7/32:ℝ)∈Ioo 0 p.t := ⟨by norm_num,by linarith⟩
  have low : (H ⟨9/16,7/32⟩).re<0 := by
    have s := early.sound (7/32) (by norm_num)
    simpa [LowSlabQuantity.holds,centralBandEdgePoint] using s
  have up : 1/4<(H ⟨11/16,7/32⟩).re := by
    have s := gate.sound (7/32) (by norm_num)
    simpa [LowSlabQuantity.holds,centralBandEdgePoint] using s
  refine ⟨up.trans ((rows _ yy) (by norm_num) (by norm_num) (by norm_num : (11/16:ℝ)<1)),?_,?_,?_⟩
  · intro x hx pos
    exact ((rows _ yy).lt_iff_lt (by norm_num) hx).mp (low.trans pos)
  · intro x hx y hy hit
    have yt : y∈Ioo 0 p.t := ⟨by linarith [hy.1],by linarith [hy.2]⟩
    have low : (H ⟨15/32,y⟩).re<0 := by
      have s := left.sound y (by norm_num; exact hy)
      simpa [LowSlabQuantity.holds,centralBandEdgePoint] using s
    have up : 1/4<(H ⟨3/5,y⟩).re := by
      have s := right.sound y (by norm_num; exact hy)
      simpa [LowSlabQuantity.holds,centralBandEdgePoint] using s
    exact ⟨(((rows y yt).lt_iff_lt (by norm_num) hx).mp (low.trans hit.1)).le,
      (((rows y yt).lt_iff_lt hx (by norm_num)).mp (hit.2.trans_lt up)).le⟩
  · intro x hx y hy hit
    obtain ⟨v,hv,val⟩ := zero y ⟨hy.1,by linarith [hy.2]⟩
    have yt : y∈Ioo 0 p.t := ⟨hy.1,by linarith [hy.2]⟩
    exact hv.1.trans (((rows y yt).lt_iff_lt (show v∈Icc (0:ℝ) 1 from
      ⟨by linarith [hv.1],hv.2.trans p.abscissa_mem.2.le⟩) hx).mp (val.trans_lt hit)).le

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_slab_height_gates
