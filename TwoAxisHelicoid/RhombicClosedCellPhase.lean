import TwoAxisHelicoid.MarkedTorusAngularEscape
import TwoAxisHelicoid.RhombicClosedAxisCell
import TwoAxisHelicoid.ClosedRectanglePhaseLift
import TwoAxisHelicoid.UnitDirectionCornerLimit

namespace TwoAxisHelicoid
open Set Complex Filter Topology
open scoped Topology

/-- The actual helicoidal phase admits a continuous real lift over the
closed fundamental rectangle. Its rotating horizontal direction agrees
with the inward transverse derivative on the finite vertical edges and
has a real unit limit at each lift of the puncture. -/
theorem marked_torus_closed_cell_phase {t α : ℝ} (ht : 0<t) (hα : α≠0)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hE : IsClosedEmbedding (harmonicTorusImmersion hX)) (b : ℝ)
    (vertical : ∀ h : ℝ, (![0,0,h] : Fin 3 → ℝ) ∈ range (harmonicTorusImmersion hX))
    (endGraph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization hα ![0,0,b] ∘ harmonicTorusImmersion hX)) :
    let P := fun w => helicoidRelativeHorizontal α b (X w)
    let D := rhombicStripDirection (-1) P
    ∃ F : unitInterval × unitInterval → ℝ, Continuous F ∧
      (∀ q, rhombicCellPoint t q ∈ regularClosedRhombicAxisCell t → exp ((F q:ℂ)*I)=D (rhombicCellPoint t q)) ∧
      (∀ q, rhombicCellPoint t q ∈ (rhombicPeriodPair t ht).lattice → Real.sin (F q)=0) := by
  let L := rhombicPeriodPair t ht
  let U := regularClosedRhombicAxisCell t
  let S := closedRhombicAxisCell t
  let p : ℂ := 0
  let q : ℂ := ⟨-1,t⟩
  let P := fun w => helicoidRelativeHorizontal α b (X w)
  let D := rhombicStripDirection (-1) P
  have strip : S ⊆ closedParameterStrip (-1) := by intro w hw; simpa [closedParameterStrip] using hw.1
  have inside {w : ℂ} (hw : w∈U) := (regularClosedRhombicAxisCell_iff ht w).mp hw
  have cn : ContinuousOn D U := fun w hw =>
    (rhombic_closed_strip_unit_direction ht hX hE.injective α b (-1) (inside hw).2 (strip (inside hw).1)).1.mono (fun _ h => strip h.1)
  have unit : ∀ w∈U, ‖D w‖=1 := fun w hw =>
    (rhombic_closed_strip_unit_direction ht hX hE.injective α b (-1) (inside hw).2 (strip (inside hw).1)).2.1
  have pole {c : ℂ} (hc : c∈L.lattice) := unit_direction_limit_on_convex (regularClosedRhombicAxisCell_convex t) cn unit
    ((marked_torus_strip_direction_im_tends_zero ht hα hX hE b (-1) vertical endGraph hc).mono_left
      (nhdsWithin_mono _ (fun w hw => (inside hw).2)))
  have qS : q∈S := ⟨⟨le_rfl,by norm_num [q]⟩,⟨ht.le,le_rfl⟩⟩
  have pS : p∈S := ⟨⟨by norm_num [p],le_rfl⟩,⟨le_rfl,ht.le⟩⟩
  have qL : q∈L.lattice := (closedRhombicAxisCell_lattice_points ht qS).mpr (Or.inr rfl)
  have pL : p∈L.lattice := L.lattice.zero_mem
  have pq : p≠q := fun e => by have := congrArg re e; norm_num [p,q] at this
  have pu : p∉U := fun h => (inside h).2 pL
  have qu : q∉U := fun h => (inside h).2 qL
  have Decomp : insert q (insert p U)=S := by
    ext w
    constructor
    · rintro (rfl | rfl | h)
      · exact qS
      · exact pS
      · exact (inside h).1
    · intro h
      by_cases hL : w∈L.lattice
      · rcases (closedRhombicAxisCell_lattice_points ht h).mp hL with e | e
        · exact Or.inr (Or.inl e)
        · exact Or.inl e
      · exact Or.inr (Or.inr ((regularClosedRhombicAxisCell_iff ht w).mpr ⟨h,hL⟩))
  obtain ⟨a,ha,ca⟩ := pole pL
  obtain ⟨d,hd,cd⟩ := pole qL
  obtain ⟨W,cW,Wreg,Wp,Wq⟩ := continuous_fill_two_points pq pu qu cn ca cd
  rw [Decomp] at cW
  have edge (w : ℂ) (hw : w∈S) (hL : w∈L.lattice) : W w=1 ∨ W w= -1 := by
    rcases (closedRhombicAxisCell_lattice_points ht hw).mp hL with e | e
    · rw [show w=p from e,Wp]; exact ha
    · rw [show w=q from e,Wq]; exact hd
  have allunit (v : unitInterval × unitInterval) : ‖W (rhombicCellPoint t v)‖=1 := by
    have mem := rhombicCellPoint_mem ht v
    by_cases lat : rhombicCellPoint t v∈L.lattice
    · rcases edge _ mem lat with h | h <;> simp [h]
    · have good := (regularClosedRhombicAxisCell_iff ht _).mpr ⟨mem,lat⟩
      rw [Wreg good]; exact unit _ good
  obtain ⟨F,cF,form⟩ := continuous_unit_square_phase (cW.comp_continuous (continuous_rhombicCellPoint t) (rhombicCellPoint_mem ht)) allunit
  refine ⟨F,cF,fun v hv => (form v).trans (Wreg hv),fun v hv => ?_⟩
  have val := congrArg im (form v)
  rw [exp_ofReal_mul_I_im] at val
  rcases edge _ (rhombicCellPoint_mem ht v) hv with h | h <;> simpa [h] using val

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_torus_closed_cell_phase
