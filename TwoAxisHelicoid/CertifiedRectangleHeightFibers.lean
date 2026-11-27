import TwoAxisHelicoid.RectangleHeightEdgeGeometry
import TwoAxisHelicoid.RectangleRowLevelGraph
import TwoAxisHelicoid.RectangleShapeLeftCover
import TwoAxisHelicoid.RectangleShapeRightCover

namespace TwoAxisHelicoid
open Complex Set Topology

/-- At every physical height the set of rows meeting the specified
closed rectangle is an interval. Between any two such rows its complete
level set is a single continuous graph, including boundary contacts. -/
theorem certified_rectangle_height_fibers :
    let p := certifiedClosedParameters
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    let Z := fun x y : ℝ => (x:ℂ)+I*y
    let F := fun x y => (H (Z x y)).re
    let C := Icc (1/2:ℝ) (5/8)
    let J := Icc (1/8:ℝ) (3/8)
    ConvexOn ℝ J (F (1/2)) ∧ StrictMonoOn (F (5/8)) J ∧
      ∀ s : ℝ, let A := {y | y∈J ∧ ∃ x∈C, F x y=s}
        Set.OrdConnected A ∧ ∀ u∈A, ∀ v∈A, u≤v →
          ∃ r : ℝ → ℝ, ContinuousOn r (Icc u v) ∧ ∀ y∈Icc u v, r y∈C ∧ ∀ x∈C, F x y=s ↔ x=r y := by
  intro p H Z F C J
  obtain ⟨cv,inc⟩ := rectangle_height_edge_shapes rectangleShapeLeftCover rectangleShapeRightCover
  refine ⟨cv,inc,?_⟩
  intro s A
  have ty : (3/8:ℝ)<p.t := (by norm_num [rootTLower] : (3/8:ℝ)<rootTLower).trans certifiedClosedParameters_bounds.1.1
  have yr {y : ℝ} (hy : y∈J) : y∈Ioo 0 p.t := ⟨by linarith [hy.1],hy.2.trans_lt ty⟩
  have off (x y : ℝ) (hy : y∈J) : Z x y∉certifiedPeriodPair.lattice := rhombic_horizontal_strip_not_mem p.height_pos (by
    change (Z x y).im∈Ioo 0 p.t
    simpa [Z] using yr hy)
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have row (y : ℝ) (hy : y∈J) : StrictMonoOn (fun x => F x y) C := by
    intro x hx w hw e
    change (H (Z x y)).re<(H (Z w y)).re
    rw [← actual_complex_height_centered_primitive p.height_pos d (off x y hy),← actual_complex_height_centered_primitive p.height_pos d (off w y hy)]
    exact sub_lt_sub_right (actual_quarter_height_row_strictMono p.height_pos (yr hy) d
      (show x∈Icc (0:ℝ) 1 from ⟨by linarith [hx.1],by linarith [hx.2]⟩)
      (show w∈Icc (0:ℝ) 1 from ⟨by linarith [hw.1],by linarith [hw.2]⟩) e) _
  have fc : ContinuousOn (fun q : ℝ × ℝ => F q.1 q.2) (C ×ˢ J) := by
    intro q h
    have l : Continuous (fun q : ℝ × ℝ => Z q.1 q.2) := by dsimp [Z]; fun_prop
    exact (continuous_re.continuousAt.comp ((actualComplexHeight_hasDerivAt (a:=p.a) (c:=1) p.height_pos (off _ _ h.2)).continuousAt.comp
      (f:=fun q : ℝ × ℝ => Z q.1 q.2) (l.continuousAt (x:=q)))).continuousWithinAt
  have lmem : (1/2:ℝ)∈C := by norm_num [C]
  have rmem : (5/8:ℝ)∈C := by norm_num [C]
  have brackets {y : ℝ} (h : y∈A) : F (1/2) y≤s ∧ s≤F (5/8) y := by
    obtain ⟨hy,x,hx,e⟩ := h
    exact ⟨((row y hy).monotoneOn lmem hx hx.1).trans_eq e,e.symm.trans_le ((row y hy).monotoneOn hx rmem hx.2)⟩
  have roots {u v : ℝ} (hu : u∈A) (hv : v∈A) : ∃ r : ℝ → ℝ, ContinuousOn r (Icc u v) ∧
      ∀ y∈Icc u v, r y∈C ∧ F (r y) y=s := by
    have sub : Icc u v⊆J := Icc_subset_Icc hu.1.1 hv.1.2
    apply rectangle_closed_row_graph (F:=fun q => F q.1 q.2) (by norm_num : (1/2:ℝ)≤5/8)
      (fc.mono (fun _ h => ⟨h.1,sub h.2⟩)) (fun y hy => row y (sub hy))
    intro y hy
    exact ⟨((cv.convex_le s).ordConnected.out ⟨hu.1,(brackets hu).1⟩ ⟨hv.1,(brackets hv).1⟩ hy).2,
      (brackets hu).2.trans (inc.monotoneOn hu.1 (sub hy) hy.1)⟩
  constructor
  · constructor
    intro u hu v hv y hy
    obtain ⟨r,_,h⟩ := roots hu hv
    exact ⟨⟨hu.1.1.trans hy.1,hy.2.trans hv.1.2⟩,r y,h y hy⟩
  · intro u hu v hv _
    obtain ⟨r,cr,h⟩ := roots hu hv
    refine ⟨r,cr,fun y hy => ⟨(h y hy).1,fun x hx => ⟨fun e => (row y ⟨hu.1.1.trans hy.1,hy.2.trans hv.1.2⟩).injOn hx (h y hy).1 (e.trans (h y hy).2.symm),fun e => e ▸ (h y hy).2⟩⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_rectangle_height_fibers
