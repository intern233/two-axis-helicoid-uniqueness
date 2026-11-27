import TwoAxisHelicoid.ClippedRectangleHarmonicMinimum
import TwoAxisHelicoid.LowerStripGaussBoundary
import TwoAxisHelicoid.CertifiedQuarterHeightRows

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- Doubling across the vertical axis puts that axis in the interior.
The sign on the zero-height arc and the certified top edge then
control the real Gauss component throughout the positive-height part
of all the lower rows, including the vertical axis. -/
theorem low_slab_real_velocity_from_boundary :
    let p := certifiedClosedParameters
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    let G := thetaGauss p.t p.a 1
    (∀ x∈Icc (1/2:ℝ) 1, (G ⟨x,3/8⟩).re<0) →
    (∀ x∈Ioo (1/2:ℝ) p.a, ∀ y∈Ioo (0:ℝ) (p.t/2), (H ⟨x,y⟩).re=0 → (G ⟨x,y⟩).re<0) →
    ∀ z : ℂ, z.re∈Icc (0:ℝ) 1 → z.im∈Ioc (0:ℝ) (3/8) → 0<(H z).re → (G z).re<0 := by
  intro p H G top central
  let X := actualGlobalImmersion p.t p.a 1 p.height_pos
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have per := actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  have lower := (by norm_num [rootTLower] : (43/50:ℝ)<rootTLower).trans certifiedClosedParameters_bounds.1.1
  have ct : (3/8:ℝ)<p.t/2 := by linarith
  have tall : (3/8:ℝ)<p.t := ct.trans (half_lt_self p.height_pos)
  obtain ⟨rows,_⟩ := certified_quarter_height_row_order
  have leftRow {y : ℝ} (hy : y∈Ioc (0:ℝ) (3/8)) :
      ∃ x∈Ioo (1/2:ℝ) p.a, (H ⟨x,y⟩).re=0 := by
    obtain ⟨u,⟨bu,hit⟩,_⟩ := certified_saddle_height_bracket.2.2 y ⟨hy.1,hy.2.trans_lt ct⟩
    have eq : (u:ℂ)+I*y=⟨u,y⟩ := by apply Complex.ext <;> simp
    have off := rhombic_horizontal_strip_not_mem (z:=(⟨u,y⟩:ℂ)) p.height_pos
      (show y∈Ioo 0 p.t from ⟨hy.1,hy.2.trans_lt tall⟩)
    refine ⟨u,bu,?_⟩
    rw [← actual_complex_height_centered_primitive p.height_pos d off]
    change X ((u:ℂ)+I*y) 2=X 1 2 at hit
    rwa [eq,← sub_eq_zero] at hit
  have low {y : ℝ} (hy : y∈Ioc (0:ℝ) (3/8)) : (H ⟨1/2,y⟩).re<0 := by
    obtain ⟨x,hx,h⟩ := leftRow hy
    exact ((rows y ⟨hy.1,hy.2.trans_lt tall⟩) (by norm_num) (show x∈Icc (0:ℝ) 1 from
      ⟨by linarith [hx.1],(hx.2.trans p.abscissa_mem.2).le⟩) hx.1).trans_eq h
  have doubled {z : ℂ} (hx : z.re∈Icc (1/2:ℝ) (3/2)) (hy : z.im∈Ioo 0 p.t)
      (edge : ∀ w : ℂ, w.re∈Icc (1/2:ℝ) 1 → w.im=z.im → (H w).re=(H z).re → (G w).re<0) :
      (G z).re<0 := by
    by_cases x : z.re≤1
    · exact edge z ⟨hx.1,x⟩ rfl rfl
    · let w := 2-conj z
      have mirror := quarter_gauss_vertical_mirror p.height_pos d per (z:=z) hy
      exact mirror.2.mp (edge w (by change (2-conj z).re∈Icc (1/2:ℝ) 1; simp; constructor <;> linarith [hx.2])
        (by simp [w]) mirror.1)
  let u := fun z : ℂ => -(G z).re
  have comp := clipped_rectangle_harmonic_positive (a:=1/2) (b:=3/2) (c:=3/8) tall
    (H:=fun z => (H z).re) (u:=u) (by
      intro z hx hy
      have off : z∉certifiedPeriodPair.lattice := by
        rcases hy.1.eq_or_lt with zero|pos
        · rw [show z=(z.re:ℂ) from Complex.ext rfl (by simp [← zero])]
          exact real_not_mem_rhombic_lattice_of_pos p.height_pos (by linarith [hx.1]) (by linarith [hx.2])
        · exact rhombic_horizontal_strip_not_mem p.height_pos ⟨pos,hy.2.trans_lt tall⟩
      exact continuous_re.continuousAt.comp (actualComplexHeight_hasDerivAt p.height_pos off).continuousAt)
    (fun _ h => gauss_real_harmonic_on_upper_strip p.height_pos h)
    ⟨⟨1,3/8⟩,⟨by norm_num,tall⟩,neg_ne_zero.mpr (top 1 (by norm_num)).ne⟩
    (lower_strip_real_gauss_boundary p.height_pos lower.le p.abscissa_mem d per) (by
      intro y hy
      have neg := (low (show y∈Ioc (0:ℝ) (3/8) from ⟨hy.1,hy.2.le⟩)).le
      have mir := (quarter_gauss_vertical_mirror p.height_pos d per (z:=(⟨1/2,y⟩:ℂ))
        (show y∈Ioo 0 p.t from ⟨hy.1,hy.2.trans tall⟩)).1
      have id : 2-conj (⟨1/2,y⟩:ℂ)=⟨3/2,y⟩ := by apply Complex.ext <;> norm_num
      exact ⟨neg,(id ▸ mir).le.trans neg⟩) (by
      intro x hx
      apply neg_nonneg.mpr
      apply le_of_lt
      apply doubled (z:=(⟨x,3/8⟩:ℂ)) hx ⟨by norm_num,tall⟩
      intro w bx wy _
      exact (show (⟨w.re,3/8⟩:ℂ)=w from Complex.ext rfl wy.symm) ▸ top w.re bx) (by
      intro z hx hy hz
      apply neg_nonneg.mpr
      apply le_of_lt
      apply doubled hx ⟨hy.1,hy.2.trans tall⟩
      intro w bx wy same
      obtain ⟨x,hx,hit⟩ := leftRow (show z.im∈Ioc (0:ℝ) (3/8) from ⟨hy.1,hy.2.le⟩)
      have zero := same.trans hz
      have eq : (⟨w.re,z.im⟩:ℂ)=w := Complex.ext rfl wy.symm
      have res := (rows z.im ⟨hy.1,hy.2.trans tall⟩).injOn (show w.re∈Icc (0:ℝ) 1 from ⟨by linarith [bx.1],bx.2⟩)
        (show x∈Icc (0:ℝ) 1 from ⟨by linarith [hx.1],(hx.2.trans p.abscissa_mem.2).le⟩)
        (by change (H ⟨w.re,z.im⟩).re=(H ⟨x,z.im⟩).re; rw [eq,zero,hit])
      exact eq ▸ central w.re (res ▸ hx) z.im ⟨hy.1,hy.2.trans ct⟩ (eq ▸ zero))
  intro z hx hy h
  have xx := ((rows z.im ⟨hy.1,hy.2.trans_lt tall⟩).lt_iff_lt (show (1/2:ℝ)∈Icc 0 1 by norm_num) hx).mp ((low hy).trans h)
  rcases hy.2.lt_or_eq with early|endrow
  · exact neg_pos.mp (comp z ⟨xx,by linarith [hx.2]⟩ ⟨hy.1,early⟩ h)
  · exact (show (⟨z.re,3/8⟩:ℂ)=z from Complex.ext rfl endrow.symm) ▸ top z.re ⟨xx.le,hx.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.low_slab_real_velocity_from_boundary
