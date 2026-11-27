import TwoAxisHelicoid.RhombicHelicoidPhase
import TwoAxisHelicoid.HelicoidBoundaryPhase
import TwoAxisHelicoid.RhombicClosedStripDirection
import TwoAxisHelicoid.RhombicWeightedHeight

namespace TwoAxisHelicoid
open Set Complex Filter Topology Metric
open scoped Topology

private theorem tangent_disks_of_local_inclusion {S T : Set ℂ} {z : ℂ}
    (d : HasInwardTangentDisksAt S z) (inc : ∀ᶠ w in 𝓝 z, w∈S → w∈T) :
    HasInwardTangentDisksAt T z := by
  obtain ⟨R,hR,ballR⟩ := Metric.mem_nhds_iff.mp inc
  intro ε hε
  obtain ⟨c,r,hr,hb,inside⟩ := d (min ε R) (lt_min hε hR)
  refine ⟨c,r,hr,hb,fun w hw => ?_⟩
  obtain ⟨hs,near⟩ := inside hw
  exact ⟨ballR (ball_subset_ball (min_le_right _ _) near) hs,ball_subset_ball (min_le_left _ _) near⟩

private theorem cell_side_has_tangent_disks {t : ℝ} {z : ℂ} (y : z.im∈Ioo 0 t)
    (side : z.re= -1 ∨ z.re=0) : HasInwardTangentDisksAt (closedRhombicAxisCell t) z := by
  have yn := (isOpen_Ioo.preimage continuous_im).mem_nhds y
  rcases side with l | r
  · apply tangent_disks_of_local_inclusion (vertical_half_planes_have_tangent_disks z).1
    have xlo : z.re<0 := by rw [l]; norm_num
    filter_upwards [yn,continuous_re.continuousAt.eventually_lt continuousAt_const xlo] with w hy hx h
    exact ⟨⟨l ▸ h,hx.le⟩,⟨hy.1.le,hy.2.le⟩⟩
  · apply tangent_disks_of_local_inclusion (vertical_half_planes_have_tangent_disks z).2
    have xhi : -1<z.re := by rw [r]; norm_num
    filter_upwards [yn,continuousAt_const.eventually_lt continuous_re.continuousAt xhi] with w hy hx h
    exact ⟨⟨hx.le,r ▸ h⟩,⟨hy.1.le,hy.2.le⟩⟩

private theorem physical_polar_of_relative {v : Fin 3 → ℝ} {α b r f : ℝ}
    (h : helicoidRelativeHorizontal α b v=(r:ℂ)*exp ((f:ℂ)*I)) :
    v 0=r*Real.cos (f+α*(v 2-b)) ∧ v 1=r*Real.sin (f+α*(v 2-b)) := by
  let a := α*(v 2-b)
  have orig : spatialGraphProjection 0 1 v=(r:ℂ)*exp (((f+a:ℝ):ℂ)*I) := by
    change exp (-(a:ℂ)*I)*spatialGraphProjection 0 1 v=_ at h
    have e := congrArg (fun w => exp ((a:ℂ)*I)*w) h
    rw [← mul_assoc,← Complex.exp_add,show (a:ℂ)*I+-(a:ℂ)*I=0 by ring,exp_zero,one_mul,
      mul_left_comm,← Complex.exp_add] at e
    convert e using 2; push_cast; ring
  change (⟨v 0,v 1⟩:ℂ)=(r:ℂ)*exp (((f+a:ℝ):ℂ)*I) at orig
  constructor
  · simpa only [re_ofReal_mul,exp_ofReal_mul_I_re] using congrArg re orig
  · simpa only [im_ofReal_mul,exp_ofReal_mul_I_im] using congrArg im orig

/-- The real phase of the corrected horizontal direction has no local
extremum at any point of intermediate height in the closed square,
including on the two finite vertical sides. -/
theorem marked_closed_cell_phase_no_extrema {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hE : IsClosedEmbedding (harmonicTorusImmersion hX)) (α b : ℝ)
    {F : unitInterval × unitInterval → ℝ} (cF : Continuous F)
    (rep : ∀ q, rhombicCellPoint t q∈regularClosedRhombicAxisCell t →
      exp ((F q:ℂ)*I)=rhombicStripDirection (-1) (fun w => helicoidRelativeHorizontal α b (X w)) (rhombicCellPoint t q)) :
    ∀ q : unitInterval × unitInterval, q.2≠0 → q.2≠1 → ¬ IsLocalExtr F q := by
  intro q y0 y1 extremum
  let z := rhombicCellPoint t q
  let L := rhombicPeriodPair t ht
  let S := closedRhombicAxisCell t
  let U := regularClosedRhombicAxisCell t
  let P := fun w => helicoidRelativeHorizontal α b (X w)
  let D := rhombicStripDirection (-1) P
  let ψ := F ∘ rhombicCellClamp t
  have sub : S ⊆ closedParameterStrip (-1) := by intro w hw; simpa [closedParameterStrip] using hw.1
  have mid : (0:ℝ)<q.2 ∧ (q.2:ℝ)<1 := ⟨lt_of_le_of_ne q.2.2.1 (fun e => y0 (Subtype.ext e.symm)),
    lt_of_le_of_ne q.2.2.2 (fun e => y1 (Subtype.ext e))⟩
  have yz : z.im∈Ioo 0 t := ⟨mul_pos ht mid.1,mul_lt_of_lt_one_right ht mid.2⟩
  have good := rhombicCell_middle_regular ht q mid
  have hz : z∉L.lattice := ((regularClosedRhombicAxisCell_iff ht _).mp good).2
  have zS : z∈S := good.1
  have cψ := cF.comp (continuous_rhombicCellClamp t)
  have hq : rhombicCellClamp t z=q := rhombicCellClamp_point ht q
  have flat : IsLocalExtr ψ z := (show IsLocalExtr F (rhombicCellClamp t z) from hq.symm ▸ extremum).comp_continuous
    (continuous_rhombicCellClamp t).continuousAt
  have polar {w : ℂ} (hw : w∈U) : exp ((ψ w:ℂ)*I)=D w ∧ P w=(‖P w‖:ℂ)*exp ((ψ w:ℂ)*I) := by
    obtain ⟨Sreg,reg⟩ := (regularClosedRhombicAxisCell_iff ht w).mp hw
    have e := rep (rhombicCellClamp t w) (by rwa [rhombicCellPoint_clamp ht Sreg])
    rw [rhombicCellPoint_clamp ht Sreg] at e
    exact ⟨e,e.symm ▸ (rhombic_closed_strip_unit_direction ht hX hE.injective α b (-1) reg (sub Sreg)).2.2⟩
  by_cases edge : z.re= -1 ∨ z.re=0
  · have disks := cell_side_has_tangent_disks yz edge
    have regular : ∀ᶠ w in 𝓝[S] z, w∈U := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (L.isClosed_lattice.isOpen_compl.mem_nhds hz)] with w hw hr
      exact (regularClosedRhombicAxisCell_iff ht w).mpr ⟨hw,hr⟩
    have near := regular.mono (fun w hw => And.intro (norm_nonneg (P w)) (polar hw).2)
    have de := (polar good).1
    change exp ((ψ z:ℂ)*I)=D z at de
    let v := fderiv ℝ P z 1
    have limit : ∃ a : ℝ, v=(a:ℂ)*exp ((ψ z:ℂ)*I) := by
      rcases edge with l | r
      · have e : exp ((ψ z:ℂ)*I)=NormedSpace.normalize v := by simpa [D,rhombicStripDirection,l,v] using de
        exact ⟨‖v‖,e.symm ▸ (NormedSpace.norm_smul_normalize v).symm⟩
      · have e : exp ((ψ z:ℂ)*I)= -NormedSpace.normalize v := by simpa [D,rhombicStripDirection,r,v] using de
        refine ⟨-‖v‖,?_⟩
        rw [e,Complex.ofReal_neg,neg_mul_neg]
        exact (NormedSpace.norm_smul_normalize v).symm
    obtain ⟨n,hn⟩ : ∃ n : ℤ, z.re=n := edge.elim (fun l => ⟨-1,by simpa using l⟩) (fun r => ⟨0,by simpa using r⟩)
    exact (marked_torus_boundary_phase_no_extremum ht hX hE α b hz hn disks cψ.continuousAt.continuousWithinAt near limit)
      (flat.isLocalExtrOn S)
  · have cell : z∈rhombicAxisRectangle (-1) t := ⟨⟨lt_of_le_of_ne zS.1.1 (fun e => edge (Or.inl e.symm)),
        by change z.re< -1+1; rw [neg_add_cancel]; exact lt_of_le_of_ne zS.1.2 (fun e => edge (Or.inr e))⟩,yz⟩
    let θ := fun w => ψ w+α*(X w 2-b)
    have ch := (continuous_apply (2 : Fin 3)).continuousAt.comp (hX.differentiable z hz).continuousAt
    have cθ : ContinuousAt θ z := cψ.continuousAt.add (continuousAt_const.mul (ch.sub continuousAt_const))
    have form : ∀ᶠ w in 𝓝 z, 0<‖P w‖ ∧ X w 0=‖P w‖*Real.cos (θ w) ∧ X w 1=‖P w‖*Real.sin (θ w) := by
      filter_upwards [(rhombicAxisRectangle_open (-1) t).mem_nhds cell] with w hw
      have closed : w∈S := ⟨⟨hw.1.1.le,by simpa using hw.1.2.le⟩,⟨hw.2.1.le,hw.2.2.le⟩⟩
      have uw := (regularClosedRhombicAxisCell_iff ht w).mpr ⟨closed,rhombic_horizontal_strip_not_mem ht hw.2⟩
      have nz : P w≠0 := mul_ne_zero (Complex.exp_ne_zero _) (marked_torus_cell_horizontal_ne_zero ht (Or.inr rfl) hX hE.injective hw)
      exact ⟨norm_pos_iff.mpr nz,physical_polar_of_relative (polar uw).2⟩
    have h := marked_torus_phase_no_interior_extremum hX hE hz cθ α b form
    have e : (fun w => θ w-α*(X w 2-b))=ψ := funext (fun _ => add_sub_cancel_right _ _)
    exact h (e.symm ▸ flat)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_closed_cell_phase_no_extrema
