import TwoAxisHelicoid.HelicoidGraphExteriorMetric
import TwoAxisHelicoid.HelicoidProjectionBound

namespace TwoAxisHelicoid
open Real Set Topology

/-- The high part of an actual C¹ helicoidal end has a connected
subset above any prescribed height which contains every sufficiently
high point. Its height is unbounded in both directions. -/
theorem HasHelicoidC1End.connected_upper_end {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (endGraph : HasHelicoidC1End X) (cont : Continuous X) :
    (∀ B : ℝ, ∃ U : Set M, IsPreconnected U ∧ (∀ x∈U,B<(X x).2) ∧
      ∃ H : ℝ, ∀ x, H<(X x).2 → x∈U) ∧
    ∀ B : ℝ, (∃ x,B<(X x).2) ∧ ∃ x,(X x).2<B := by
  obtain ⟨C,_,R,_,core,E,_,u,_,graph,_⟩ := endGraph
  let S := helicoidProjectedEnd X C (exteriorPlaneBase R)
  let chartPoint := fun p : exteriorPlaneBase R => (E.symm p).1
  have cs : Continuous chartPoint := continuous_subtype_val.comp E.symm.continuous
  have close (p : exteriorPlaneBase R) : |(X (chartPoint p)).2-p.1.2|≤1 := by
    have eq := congrArg Prod.snd (graph p).2
    change (X (chartPoint p)).2=p.1.2+helicoidAngle p.1.1 (u p) at eq
    rw [eq,add_sub_cancel_left]
    exact helicoidAngle_abs_le ((graph p).1.trans (by norm_num))
  have outside {x y : ℝ} (hy : R<y) : (x,y)∈exteriorPlaneBase R :=
    hy.trans_le ((le_abs_self y).trans (by simpa only [Real.norm_eq_abs] using norm_snd_le (x,y)))
  obtain ⟨D,bd⟩ := core.exists_bound_of_continuousOn (continuous_snd.comp cont).continuousOn
  constructor
  · intro B
    let T := max R (B+2)
    let j := fun p : ℝ × Ioi T => (⟨(p.1,p.2.1),outside ((le_max_left _ _).trans_lt p.2.2)⟩ : exteriorPlaneBase R)
    have cj : Continuous j := Continuous.subtype_mk (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)) _
    let : PreconnectedSpace (Ioi T) := Subtype.preconnectedSpace isPreconnected_Ioi
    let U := range (chartPoint ∘ j)
    refine ⟨U,isPreconnected_range (cs.comp cj),?_,max D (T+1),?_⟩
    · rintro _ ⟨p,rfl⟩
      have lower := (abs_le.mp (close (j p))).1
      change -1≤(X (chartPoint (j p))).2-p.2.1 at lower
      have ht : B+2<p.2.1 := (le_max_right R (B+2)).trans_lt p.2.2
      change B<(X (chartPoint (j p))).2
      linarith
    · intro x high
      have sx : x∈S := by
        by_contra hn
        have bd' : ‖(X x).2‖≤D := bd x hn
        exact (not_le_of_gt ((le_max_left D (T+1)).trans_lt high))
          ((le_abs_self (X x).2).trans (by simpa only [Real.norm_eq_abs] using bd'))
      let p := E ⟨x,sx⟩
      have xeq : chartPoint p=x := congrArg Subtype.val (E.symm_apply_apply ⟨x,sx⟩)
      have upper := (abs_le.mp (close p)).2
      rw [xeq] at upper
      have ht : T<p.1.2 := by linarith [(le_max_right D (T+1)).trans_lt high]
      exact ⟨(p.1.1,⟨p.1.2,ht⟩),xeq⟩
  · intro B
    let y := |B|+|R|+2
    have yr : R<y := by dsimp [y]; linarith [le_abs_self R,abs_nonneg B]
    let p : exteriorPlaneBase R := ⟨(0,y),outside yr⟩
    have off : (0,-y)∈exteriorPlaneBase R := by
      change R<‖((0:ℝ),-y)‖
      have h : y≤‖-y‖ := by rw [norm_neg,Real.norm_eq_abs]; exact le_abs_self _
      exact yr.trans_le (h.trans (norm_snd_le ((0:ℝ),-y)))
    let q : exteriorPlaneBase R := ⟨(0,-y),off⟩
    refine ⟨⟨chartPoint p,?_⟩,⟨chartPoint q,?_⟩⟩
    · have h := (abs_le.mp (close p)).1
      change -1≤(X (chartPoint p)).2-(|B|+|R|+2) at h
      linarith [le_abs_self B,abs_nonneg R]
    · have h := (abs_le.mp (close q)).2
      change (X (chartPoint q)).2-(-(|B|+|R|+2))≤1 at h
      linarith [neg_le_abs B,abs_nonneg R]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.connected_upper_end
