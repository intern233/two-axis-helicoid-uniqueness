import TwoAxisHelicoid.HorizontalFiberTurningCircle
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ReImTopology

namespace TwoAxisHelicoid
open Complex Set Topology Bornology
open scoped ComplexOrder

/-- Two componentwise upper bounds for a holomorphic function on the
four sides of a closed rectangle hold on the entire rectangle. -/
theorem complex_rectangle_component_bounds {a b c d M : ℝ} (ab : a≤b) (cd : c≤d) {g : ℂ → ℂ}
    (diff : ∀ z : ℂ, z.re∈Icc a b → z.im∈Icc c d → DifferentiableAt ℂ g z)
    (vert : ∀ x∈({a,b}:Set ℝ), ∀ y∈Icc c d, (g ⟨x,y⟩).re≤M ∧ (g ⟨x,y⟩).im≤M)
    (horiz : ∀ y∈({c,d}:Set ℝ), ∀ x∈Icc a b, (g ⟨x,y⟩).re≤M ∧ (g ⟨x,y⟩).im≤M) :
    ∀ z : ℂ, z.re∈Icc a b → z.im∈Icc c d → (g z).re≤M ∧ (g z).im≤M := by
  let R := (Icc a b) ×ℂ (Icc c d)
  have bd : IsBounded R := (isCompact_Icc : IsCompact (Icc a b)).isBounded.reProdIm (isCompact_Icc : IsCompact (Icc c d)).isBounded
  have cl : closure R=R := by simp only [R,closure_reProdIm,closure_Icc]
  have boundary (z : ℂ) (hz : z∈frontier R) : (g z).re≤M ∧ (g z).im≤M := by
    change z∈frontier ((Icc a b) ×ℂ (Icc c d)) at hz
    rw [frontier_reProdIm,closure_Icc,closure_Icc,frontier_Icc ab,frontier_Icc cd] at hz
    rcases hz with h|h
    · exact horiz z.im h.2 z.re h.1
    · exact vert z.re h.1 z.im h.2
  have maxRe (f : ℂ → ℂ) (df : ∀ z∈R, DifferentiableAt ℂ f z) (B : ∀ z∈frontier R, (f z).re≤M)
      {z : ℂ} (hz : z∈R) : (f z).re≤M := by
    let h := fun w => exp (f w)
    have dh : DiffContOnCl ℂ h R := ⟨fun w hw => (df w hw).cexp.differentiableWithinAt,by
      rw [cl]; exact fun w hw => (df w hw).cexp.continuousAt.continuousWithinAt⟩
    have e := norm_le_of_forall_mem_frontier_norm_le bd dh (C:=Real.exp M)
      (fun w hw => by change ‖exp (f w)‖≤_; rw [norm_exp]; exact Real.exp_le_exp.mpr (B w hw))
      (cl.symm ▸ hz)
    exact Real.exp_le_exp.mp (by simpa only [h,norm_exp] using e)
  intro z hx hy
  have hz : z∈R := ⟨hx,hy⟩
  have f (w : ℂ) (hw : w∈R) := diff w hw.1 hw.2
  refine ⟨maxRe g f (fun w hw => (boundary w hw).1) hz,?_⟩
  have j := maxRe (fun w => -I*g w) (fun w hw => (f w hw).const_mul (-I)) (fun w hw => by
    simpa only [neg_mul,neg_re,I_mul_re,neg_neg] using (boundary w hw).2) hz
  simpa only [neg_mul,neg_re,I_mul_re,neg_neg] using j

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.complex_rectangle_component_bounds
