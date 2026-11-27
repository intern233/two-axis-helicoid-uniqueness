import TwoAxisHelicoid.BoundedHarmonicStripMinimum
import Mathlib.Analysis.Complex.ReImTopology

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped ComplexOrder

/-- Comparison in a rectangle intersected with a positive superlevel
set. Boundary poles are allowed along the bottom when their lower
limits from the upper strip are nonnegative. -/
theorem clipped_rectangle_harmonic_positive {a b c t : ℝ} (ct : c<t)
    {H u : ℂ → ℝ} (hcont : ∀ z : ℂ, z.re∈Icc a b → z.im∈Icc 0 c → ContinuousAt H z)
    (harm : ∀ z : ℂ, z.im∈Ioo (0:ℝ) t → HarmonicAt u z)
    (nonzero : ∃ z : ℂ, z.im∈Ioo (0:ℝ) t ∧ u z≠0)
    (bottom : ∀ x∈Icc a b, ∀ e : ℝ, 0<e →
      ∀ᶠ w in 𝓝[{z : ℂ | z.im∈Ioo (0:ℝ) t}] (x:ℂ), -e≤u w)
    (sides : ∀ y∈Ioo (0:ℝ) c, H ⟨a,y⟩≤0 ∧ H ⟨b,y⟩≤0)
    (top : ∀ x∈Icc a b, 0≤u ⟨x,c⟩)
    (level : ∀ z : ℂ, z.re∈Icc a b → z.im∈Ioo (0:ℝ) c → H z=0 → 0≤u z) :
    ∀ z : ℂ, z.re∈Ioo a b → z.im∈Ioo (0:ℝ) c → 0<H z → 0<u z := by
  let C := (Icc a b) ×ℂ (Icc (0:ℝ) c)
  let Q := (Ioo a b) ×ℂ (Ioo (0:ℝ) c)
  let U := Q∩H ⁻¹' Ioi 0
  let V := {z : ℂ | z.im∈Ioo (0:ℝ) t}
  have contained : U⊆C := fun z hz => ⟨Ioo_subset_Icc_self hz.1.1,Ioo_subset_Icc_self hz.1.2⟩
  have inside : U⊆V := fun z hz => ⟨hz.1.2.1,hz.1.2.2.trans ct⟩
  have compact : IsCompact C := (isCompact_Icc : IsCompact (Icc a b)).reProdIm isCompact_Icc
  have qopen : IsOpen Q := (isOpen_Ioo.preimage continuous_re).inter (isOpen_Ioo.preimage continuous_im)
  have op : IsOpen U := isOpen_iff_mem_nhds.mpr (by
    intro z hz
    have pos := (hcont z (contained hz).1 (contained hz).2).eventually (Ioi_mem_nhds hz.2)
    exact inter_mem (qopen.mem_nhds hz.1) pos)
  have cv : Convex ℝ V := (convex_Ioo (0:ℝ) t).linear_preimage imCLM.toLinearMap
  have edge (z : ℂ) (hz : z∈frontier U) (e : ℝ) (ep : 0<e) : ∀ᶠ w in 𝓝[U] z, -e≤u w := by
    have cc : z∈C := closure_minimal contained compact.isClosed hz.1
    have : NeBot (𝓝[U] z) := mem_closure_iff_nhdsWithin_neBot.mp hz.1
    have nearby : ∀ᶠ w in 𝓝[U] z, w∈U := self_mem_nhdsWithin
    have gate : 0≤H z := isClosed_Ici.mem_of_tendsto ((hcont z cc.1 cc.2).tendsto.mono_left nhdsWithin_le_nhds)
      (nearby.mono fun w hw => (show 0<H w from hw.2).le)
    rcases cc.2.1.eq_or_lt with zero|pos
    · have real : (z.re:ℂ)=z := Complex.ext rfl zero
      have lower := bottom z.re cc.1 e ep
      rw [real] at lower
      exact lower.filter_mono (nhdsWithin_mono _ inside)
    have reg : z.im∈Ioo 0 t := ⟨pos,cc.2.2.trans_lt ct⟩
    have val : 0≤u z := by
      rcases cc.2.2.lt_or_eq with low|atTop
      · have row : z.im∈Ioo 0 c := ⟨pos,low⟩
        rcases gate.eq_or_lt with eq|high
        · exact level z cc.1 row eq.symm
        · have strict : z.re∈Ioo a b := by
            refine ⟨lt_of_le_of_ne cc.1.1 (fun eq => ?_),lt_of_le_of_ne cc.1.2 (fun eq => ?_)⟩
            · exact high.not_ge (by simpa only [eq,Complex.eta] using (sides z.im row).1)
            · exact high.not_ge (by simpa only [← eq,Complex.eta] using (sides z.im row).2)
          exact (hz.2 (op.interior_eq.symm ▸ (show z∈U from ⟨⟨strict,row⟩,high⟩))).elim
      · have eq : (⟨z.re,c⟩:ℂ)=z := Complex.ext rfl atTop.symm
        exact eq ▸ top z.re cc.1
    exact (((harm z reg).1.continuousAt.eventually (Ioi_mem_nhds (show -e<u z by linarith))).filter_mono
      nhdsWithin_le_nhds).mono fun _ h => h.le
  intro z x y height
  exact bounded_domain_harmonic_pos op (compact.isBounded.subset contained) inside cv.isPreconnected harm
    nonzero edge z ⟨⟨x,y⟩,height⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.clipped_rectangle_harmonic_positive
