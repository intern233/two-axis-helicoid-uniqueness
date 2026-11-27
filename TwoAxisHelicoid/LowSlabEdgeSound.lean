import TwoAxisHelicoid.LowSlabEdgeData

namespace TwoAxisHelicoid
open Complex Set ComplexBall

theorem low_slab_edge_contains {v : Bool} {e l r : ℚ} {x : ℝ} (hx : x∈Icc (l:ℝ) r) :
    (centralBandEdgeBall v e l r).Contains (centralBandEdgePoint v e x) := by
  cases v
  · have d := rectangle_center_disk_contains hx (show (e:ℝ)∈Icc (e:ℝ) e from ⟨le_rfl,le_rfl⟩)
    rw [show (x:ℂ)+I*(e:ℝ)=⟨x,(e:ℝ)⟩ by apply Complex.ext <;> simp] at d
    simpa [centralBandEdgeBall,centralBandEdgePoint] using d
  · have d := rectangle_center_disk_contains (show (e:ℝ)∈Icc (e:ℝ) e from ⟨le_rfl,le_rfl⟩) hx
    rw [show ((e:ℝ):ℂ)+I*x=⟨(e:ℝ),x⟩ by apply Complex.ext <;> simp] at d
    simpa [centralBandEdgeBall,centralBandEdgePoint] using d

noncomputable def LowSlabQuantity.holds (k : LowSlabQuantity) (z : ℂ) : Prop :=
  let p := certifiedClosedParameters
  match k with
  | .sector => ∀ u : ℝ, |u|≤1 → let F := centralPhaseThetaRatio p.t p.a z
                4*F.re+u*F.im≤ -(1/1024:ℝ)
  | .height a m => let h := (actualComplexHeight p.t p.a 1 p.height_pos z).re
                   if a then (m:ℝ)<h else h<(m:ℝ)

theorem CheckedLowSlabEdge.sound {k v e l r} (cert : CheckedLowSlabEdge k v e l r) :
    ∀ x∈Icc (l:ℝ) r, k.holds (centralBandEdgePoint v e x) := by
  let p := certifiedClosedParameters
  have tb := Ioo_subset_Icc_self certifiedClosedParameters_bounds.1
  have ab := Ioo_subset_Icc_self certifiedClosedParameters_bounds.2
  induction cert with
  | @sector v e l r w ok =>
    intro x hx u hu F
    obtain ⟨valid,box,margin⟩ := ok
    let B := w.value.output.toBall slopingFluxAnalyticSetup.config.prec
    let c := (B.center.im:ℝ)
    have encl : B.Contains F := w.encloses tb ab (coarsen_contains (low_slab_edge_contains hx) box) valid
    have re := (re_bounds encl).2
    change F.re≤((B.center.re+B.radius:ℚ):ℝ) at re
    push_cast at re
    have im := (Complex.abs_im_le_norm (F-B.center.val)).trans encl
    change |F.im-c|≤(B.radius:ℝ) at im
    have norm : |F.im|≤B.radius+|c| := calc
      |F.im| = |F.im-c+c| := by rw [sub_add_cancel]
      _ ≤ |F.im-c|+|c| := abs_add_le _ _
      _ ≤ _ := add_le_add_left im _
    have scalar : u*F.im≤|F.im| := (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hu)
    have m : 4*(B.center.re:ℝ)+|c|+5*B.radius≤ -(1/1024:ℝ) := by
      change 4*B.center.re+|B.center.im|+5*B.radius≤ -(1/1024:ℚ) at margin
      have b := Rat.cast_le (K:=ℝ) |>.mpr margin
      push_cast at b
      exact b
    linarith
  | @height a v m e l r w ok =>
    intro x hx
    obtain ⟨valid,box,margin⟩ := ok
    obtain ⟨lo,q,_,_⟩ := sloping_flux_root_parameter_enclosures tb ab
    have b := (w.sound slopingFluxAnalyticSetup slopingFluxAnalyticSetup_valid valid p.height_pos p.abscissa_mem
      p.vertical_closed lo (central_trace_height_parameter tb) q (coarsen_contains (low_slab_edge_contains hx) box)).2
    obtain ⟨low,high⟩ := re_bounds b
    cases a
    · exact high.trans_lt (Rat.cast_lt.mpr margin)
    · exact lt_of_lt_of_le (Rat.cast_lt.mpr margin) low
  | @join k v e l m r _ _ first last =>
    intro x hx
    rcases le_total x (m:ℝ) with lo|hi
    · exact first x ⟨hx.1,lo⟩
    · exact last x ⟨hi,hx.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CheckedLowSlabEdge.sound
