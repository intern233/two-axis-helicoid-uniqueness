import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ReImTopology

namespace TwoAxisHelicoid
open Complex Set Topology Bornology
open scoped ComplexOrder

/-- A lower bound on the real part on all four edges extends across the rectangle. -/
theorem rectangle_real_lower_bound {a b c d m : ℝ} (ab : a≤b) (cd : c≤d) {f : ℂ → ℂ}
    (diff : ∀ z : ℂ, z.re∈Icc a b → z.im∈Icc c d → DifferentiableAt ℂ f z)
    (vert : ∀ x∈({a,b}:Set ℝ), ∀ y∈Icc c d, m≤(f ⟨x,y⟩).re)
    (horiz : ∀ y∈({c,d}:Set ℝ), ∀ x∈Icc a b, m≤(f ⟨x,y⟩).re) :
    ∀ z : ℂ, z.re∈Icc a b → z.im∈Icc c d → m≤(f z).re := by
  let U := (Icc a b) ×ℂ (Icc c d)
  have bd : IsBounded U := (isCompact_Icc : IsCompact (Icc a b)).isBounded.reProdIm
    (isCompact_Icc : IsCompact (Icc c d)).isBounded
  have cl : closure U=U := by simp [U,closure_reProdIm,closure_Icc]
  have boundary {z : ℂ} (h : z∈frontier U) : m≤(f z).re := by
    change z∈frontier ((Icc a b) ×ℂ (Icc c d)) at h
    rw [frontier_reProdIm,closure_Icc,closure_Icc,frontier_Icc ab,frontier_Icc cd] at h
    rcases h with h|h
    · exact horiz z.im h.2 z.re h.1
    · exact vert z.re h.1 z.im h.2
  let g := fun w => exp (-(f w))
  have dg : DiffContOnCl ℂ g U := ⟨fun w h => (diff w h.1 h.2).neg.cexp.differentiableWithinAt,by
    rw [cl]; exact fun w h => (diff w h.1 h.2).neg.cexp.continuousAt.continuousWithinAt⟩
  intro z hx hy
  have p := norm_le_of_forall_mem_frontier_norm_le bd dg (C:=Real.exp (-m)) (fun w hw => by
    change ‖exp (-(f w))‖≤_
    rw [norm_exp,neg_re,Real.exp_le_exp]
    exact neg_le_neg (boundary hw)) ((cl.symm ▸ (show z∈U from ⟨hx,hy⟩)) : z∈closure U)
  rwa [show g z=exp (-(f z)) from rfl,norm_exp,neg_re,Real.exp_le_exp,neg_le_neg_iff] at p

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangle_real_lower_bound
