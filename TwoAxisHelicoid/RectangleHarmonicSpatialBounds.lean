import TwoAxisHelicoid.SurfaceHarmonicComparison
import Mathlib.Analysis.Complex.ReImTopology

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped ComplexOrder

/-- When opposite edges have opposite orders, the lower bound of a
harmonic coordinate throughout a closed rectangle is attained at
one of the two diagonally opposite corners. -/
theorem harmonic_rectangle_lower_from_corners {a b c d : ℝ} {u : ℂ → ℝ}
    (harm : ∀ z : ℂ, z.re∈Icc a b → z.im∈Icc c d → HarmonicAt u z)
    (left : AntitoneOn (fun y => u ⟨a,y⟩) (Icc c d))
    (right : MonotoneOn (fun y => u ⟨b,y⟩) (Icc c d))
    (bottom : AntitoneOn (fun x => u ⟨x,c⟩) (Icc a b))
    (top : MonotoneOn (fun x => u ⟨x,d⟩) (Icc a b)) :
    ∀ z : ℂ, z.re∈Icc a b → z.im∈Icc c d → min (u ⟨b,c⟩) (u ⟨a,d⟩)≤u z := by
  let K := (Icc a b) ×ℂ (Icc c d)
  let Q := (Ioo a b) ×ℂ (Ioo c d)
  let m := min (u ⟨b,c⟩) (u ⟨a,d⟩)
  let f := fun z : ℂ => m-u z
  have compact : IsCompact K := (isCompact_Icc : IsCompact (Icc a b)).reProdIm isCompact_Icc
  have hf {z : ℂ} (hz : z∈K) : HarmonicAt f z := (harmonicAt_const m).sub (harm z hz.1 hz.2)
  have op : IsOpen Q := (isOpen_Ioo.preimage continuous_re).inter (isOpen_Ioo.preimage continuous_im)
  have sub : Q⊆K := fun z hz => ⟨Ioo_subset_Icc_self hz.1,Ioo_subset_Icc_self hz.2⟩
  have bound (z : ℂ) (hz : z∈K) (border : z∉interior K) : f z≤0 := by
    apply sub_nonpos.mpr
    have ab := hz.1.1.trans hz.1.2
    have cd := hz.2.1.trans hz.2.2
    rcases hz.1.1.eq_or_lt with lo|lo
    · have p : (⟨a,z.im⟩:ℂ)=z := Complex.ext lo rfl
      exact p ▸ (min_le_right _ _).trans (left hz.2 ⟨cd,le_rfl⟩ hz.2.2)
    rcases hz.1.2.lt_or_eq with hi|hi
    · rcases hz.2.1.eq_or_lt with bot|bot
      · have p : (⟨z.re,c⟩:ℂ)=z := Complex.ext rfl bot
        exact p ▸ (min_le_left _ _).trans (bottom hz.1 ⟨ab,le_rfl⟩ hz.1.2)
      rcases hz.2.2.lt_or_eq with up|up
      · exact (border (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
          (op.mem_nhds (show z∈Q from ⟨⟨lo,hi⟩,bot,up⟩)) sub))).elim
      · have p : (⟨z.re,d⟩:ℂ)=z := Complex.ext rfl up.symm
        exact p ▸ (min_le_right _ _).trans (top ⟨le_rfl,ab⟩ hz.1 hz.1.1)
    · have p : (⟨b,z.im⟩:ℂ)=z := Complex.ext hi.symm rfl
      exact p ▸ (min_le_left _ _).trans (right ⟨le_rfl,cd⟩ hz.2 hz.2.1)
  have everywhere := compact_boundary_maximum_principle compact (fun z hz => (hf hz).1.continuousAt.continuousWithinAt)
    bound (fun z hz _ mx => harmonic_eventually_constant_at_local_max (hf (interior_subset hz)) mx)
  intro z hx hy
  exact sub_nonpos.mp (everywhere z ⟨hx,hy⟩)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_rectangle_lower_from_corners
