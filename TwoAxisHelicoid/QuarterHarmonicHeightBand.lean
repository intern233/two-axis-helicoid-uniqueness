import TwoAxisHelicoid.BoundedHarmonicStripMinimum
import TwoAxisHelicoid.QuarterTransverseBoundary
import TwoAxisHelicoid.PositiveStripCorner
import Mathlib.Analysis.Complex.ReImTopology

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology InnerProductSpace
open scoped Topology ComplexOrder

/-- Positivity on the lower and upper level arcs extends to the whole
positive height band of the first quarter. The harmonic comparison
uses the genuine two-axis boundary and the one-sided puncture estimate. -/
theorem quarter_harmonic_height_band {t a s : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (bound : s≤1/(2*(1-a))) {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z)
    (harm : ∀ z∉(rhombicPeriodPair t ht).lattice, HarmonicAt (fun w => X w 1-X 1 1) z)
    (witness : ∃ z∉(rhombicPeriodPair t ht).lattice, X z 1≠X 1 1)
    (arcs : ∀ z : ℂ, z.re∈Ioo (0:ℝ) 1 → z.im∈Ioo (0:ℝ) t →
      (X z 2=X 1 2 ∨ X z 2=X 1 2+s) → X 1 1≤X z 1) :
    ∀ z : ℂ, z.re∈Ioo (0:ℝ) 1 → z.im∈Ioo (0:ℝ) t → X z 2-X 1 2∈Ioo (0:ℝ) s → X 1 1<X z 1 := by
  let L := rhombicPeriodPair t ht
  let H := fun z : ℂ => X z 2-X 1 2
  let Y := fun z : ℂ => X z 1-X 1 1
  let Q := (Ioo (0:ℝ) 1) ×ℂ (Ioo (0:ℝ) t)
  let C := (Icc (0:ℝ) 1) ×ℂ (Icc (0:ℝ) t)
  let U := Q∩H ⁻¹' Ioo (0:ℝ) s
  have regular {z : ℂ} (h : z∈Q) : z∉L.lattice := rhombic_horizontal_strip_not_mem ht h.2
  have hCont {z : ℂ} (r : z∉L.lattice) : ContinuousAt H z :=
    (actual_coordinate_primitive_component ht d r 2).continuousAt.sub continuousAt_const
  have qOpen : IsOpen Q := (isOpen_Ioo.preimage continuous_re).inter (isOpen_Ioo.preimage continuous_im)
  have op : IsOpen U := isOpen_iff_mem_nhds.mpr (by
    intro z hz
    exact inter_mem (qOpen.mem_nhds hz.1) ((hCont (regular hz.1)).eventually (isOpen_Ioo.mem_nhds hz.2)))
  have usub : U⊆C := fun _ hu => ⟨Ioo_subset_Icc_self hu.1.1,Ioo_subset_Icc_self hu.1.2⟩
  have compact : IsCompact C := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).reProdIm isCompact_Icc
  have edge (z : ℂ) (hz : z∈frontier U) (e : ℝ) (ep : 0<e) : ∀ᶠ w in 𝓝[U] z, -e≤Y w := by
    have cc := closure_minimal usub compact.isClosed hz.1
    have onSet : ∀ᶠ w in 𝓝[U] z, w∈U := self_mem_nhdsWithin
    by_cases off : z∉L.lattice
    · have : NeBot (𝓝[U] z) := mem_closure_iff_nhdsWithin_neBot.mp hz.1
      have hval : H z∈Icc (0:ℝ) s := isClosed_Icc.mem_of_tendsto ((hCont off).tendsto.mono_left nhdsWithin_le_nhds)
        (onSet.mono fun w hw => Ioo_subset_Icc_self hw.2)
      have pos : 0≤Y z := by
        by_cases inside : z∈Q
        · have terminal : H z=0 ∨ H z=s := by
            rcases hval.1.eq_or_lt with lo|lo
            · exact Or.inl lo.symm
            rcases hval.2.lt_or_eq with hi|hi
            · exact (hz.2 (op.interior_eq.symm ▸ (show z∈U from ⟨inside,lo,hi⟩))).elim
            · exact Or.inr hi
          apply sub_nonneg.mpr (arcs z inside.1 inside.2 ?_)
          rcases terminal with eq|eq
          · exact Or.inl (sub_eq_zero.mp eq)
          · exact Or.inr (by change X z 2-X 1 2=s at eq; linarith)
        · have sides : z.re=0 ∨ z.re=1 ∨ z.im=0 ∨ z.im=t := by
            by_contra! bad
            exact inside ⟨⟨lt_of_le_of_ne cc.1.1 (Ne.symm bad.1),lt_of_le_of_ne cc.1.2 bad.2.1⟩,
              ⟨lt_of_le_of_ne cc.2.1 (Ne.symm bad.2.2.1),lt_of_le_of_ne cc.2.2 bad.2.2.2⟩⟩
          exact sub_nonneg.mpr ((quarter_rectangle_punctures_and_axes ht d per cc.1 cc.2).2 off sides).ge
      exact (((harm z off).1.continuousAt.eventually (Ioi_mem_nhds (show -e<Y z by linarith))).filter_mono
        nhdsWithin_le_nhds).mono fun _ h => h.le
    · rcases (quarter_rectangle_punctures_and_axes ht d per cc.1 cc.2).1 (not_not.mp off) with origin|top
      · subst z
        have near := (quarter_positive_height_avoids_origin ht ha d per).filter_mono
          (nhdsWithin_le_nhds (s:=U) (a:=(0:ℂ)))
        filter_upwards [near,onSet] with w neg hw
        exact False.elim ((neg hw.1.1 hw.1.2).not_ge (sub_pos.mp hw.2.1).le)
      · subst z
        have outsidePoint : U⊆{(1+I*(t:ℂ))}ᶜ := by
          intro w hw eq
          have ident : w=1+I*t := eq
          have low := hw.1.1.2
          rw [ident] at low
          simp at low
        have near := (quarter_upper_puncture_transverse_positive ht ha d per).filter_mono (nhdsWithin_mono _ outsidePoint)
        filter_upwards [near,onSet] with w positive hw
        have gt := positive hw.1.1.2.le ⟨hw.2.1,hw.2.2.le.trans bound⟩
        exact (neg_nonpos.mpr ep.le).trans (sub_nonneg.mpr gt.le)
  obtain ⟨v,hv,w⟩ := witness
  have result := bounded_domain_harmonic_pos op (compact.isBounded.subset usub) (V:=L.latticeᶜ)
    (fun _ hu => regular hu.1) (rhombic_punctured_plane_isConnected ht).2 harm
    ⟨v,hv,sub_ne_zero.mpr w⟩ edge
  intro z zx zy level
  exact sub_pos.mp (result z ⟨⟨zx,zy⟩,level⟩)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarter_harmonic_height_band
