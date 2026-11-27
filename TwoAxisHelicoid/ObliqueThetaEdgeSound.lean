import TwoAxisHelicoid.ObliqueThetaEdgeData

namespace TwoAxisHelicoid
open Complex Set ComplexBall

/-- The two projections are conjugate, as required by the horizontal half turn. -/
noncomputable def obliqueThetaFactor (positive : Bool) : ℂ := if positive then ⟨4,7⟩ else ⟨4,-7⟩

theorem CheckedObliqueEdge.sound {pos h v e l r} (cert : CheckedObliqueEdge pos h v e l r) :
    let p := certifiedClosedParameters
    ∀ u∈Icc (l:ℝ) r, let z := centralBandEdgePoint v e u
      if h then (if pos then (actualComplexHeight p.t p.a 1 p.height_pos z).re else
        -(actualComplexHeight p.t p.a 1 p.height_pos z).re)<1/4 else
        (obliqueThetaFactor pos*centralPhaseThetaRatio p.t p.a z).re ≤ -(1/1024:ℝ) := by
  intro p
  have tb := Ioo_subset_Icc_self certifiedClosedParameters_bounds.1
  have ab := Ioo_subset_Icc_self certifiedClosedParameters_bounds.2
  have edge {v : Bool} {e l r : ℚ} {x : ℝ} (hx : x∈Icc (l:ℝ) r) :
      (centralBandEdgeBall v e l r).Contains (centralBandEdgePoint v e x) := by
    cases v
    · have d := rectangle_center_disk_contains hx (show (e:ℝ)∈Icc (e:ℝ) e from ⟨le_rfl,le_rfl⟩)
      rw [show (x:ℂ)+I*(e:ℝ)=⟨x,(e:ℝ)⟩ by apply Complex.ext <;> simp] at d
      simpa [centralBandEdgeBall,centralBandEdgePoint] using d
    · have d := rectangle_center_disk_contains (show (e:ℝ)∈Icc (e:ℝ) e from ⟨le_rfl,le_rfl⟩) hx
      rw [show ((e:ℝ):ℂ)+I*x=⟨(e:ℝ),x⟩ by apply Complex.ext <;> simp] at d
      simpa [centralBandEdgeBall,centralBandEdgePoint] using d
  induction cert with
  | @ratio v e l r w ok =>
    intro u hu z
    obtain ⟨valid,box,margin⟩ := ok
    have b := w.encloses tb ab (coarsen_contains (edge hu) box) valid
    let B := w.value.output.toBall slopingFluxAnalyticSetup.config.prec
    let F := centralPhaseThetaRatio p.t p.a z
    change B.Contains F at b
    have br := (re_bounds b).2
    have im := (Complex.abs_im_le_norm (F-B.center.val)).trans b
    change |F.im-(B.center.im:ℝ)|≤(B.radius:ℝ) at im
    change F.re≤((B.center.re+B.radius:ℚ):ℝ) at br
    push_cast at br
    change 4*B.center.re+(if pos then -7 else 7)*B.center.im+11*B.radius≤ -(1/1024:ℚ) at margin
    change (obliqueThetaFactor pos*F).re≤ -(1/1024:ℝ)
    cases pos <;> norm_num [obliqueThetaFactor,Complex.mul_re] at margin ⊢
    all_goals
      have m := Rat.cast_le (K:=ℝ) |>.mpr margin
      push_cast at m
      linarith [(abs_le.mp im).1,(abs_le.mp im).2]
  | @height v e l r w ok =>
    intro u hu z
    obtain ⟨valid,box,margin⟩ := ok
    obtain ⟨lo,q,_,_⟩ := sloping_flux_root_parameter_enclosures tb ab
    have b := (w.sound slopingFluxAnalyticSetup slopingFluxAnalyticSetup_valid valid p.height_pos p.abscissa_mem
      p.vertical_closed lo (central_trace_height_parameter tb) q
      (coarsen_contains (edge hu) box)).2
    let B := w.height.output.toBall slopingFluxAnalyticSetup.config.prec
    let H := actualComplexHeight p.t p.a 1 p.height_pos z
    change B.Contains H at b
    have rb := re_bounds b
    change (if pos then B.center.re else -B.center.re)+B.radius<1/4 at margin
    change (if pos then H.re else -H.re)<1/4
    cases pos <;> simp only [Bool.false_eq_true,ite_false,ite_true] at margin ⊢
    all_goals
      have m := Rat.cast_lt (K:=ℝ) |>.mpr margin
      push_cast at m rb
      linarith [rb.1,rb.2]
  | @join h v e l m r _ _ left right =>
    intro u hu
    rcases le_total u (m:ℝ) with low|high
    · exact left u ⟨hu.1,low⟩
    · exact right u ⟨high,hu.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CheckedObliqueEdge.sound
