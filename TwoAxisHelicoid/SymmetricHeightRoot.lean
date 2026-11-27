import TwoAxisHelicoid.SymmetricHeightZero
import TwoAxisHelicoid.RhombicHeightRoot

namespace TwoAxisHelicoid
open Complex Set

theorem symmetric_height_has_normalized_real_zero {t : ℝ} (ht : 0 < t)
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential (rhombicPeriodPair t ht) p)
    {K u : ℂ} (hK : K ≠ 0)
    (hheight : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      p z 2 = K*((rhombicPeriodPair t ht).weierstrassP z-u)) :
    ∃ a : ℝ, a ∈ Ioo (0 : ℝ) 1 ∧ p a 2 = 0 := by
  let L := rhombicPeriodPair t ht
  obtain ⟨x,hxn,hxz,_⟩ := symmetric_height_has_real_zero ht hp hK hheight
  let n : ℤ := ⌊x/2⌋
  let r : ℝ := x-2*(n : ℝ)
  have hr0 : 0 ≤ r := by dsimp [r,n]; linarith [Int.floor_le (x/2)]
  have hr2 : r < 2 := by dsimp [r,n]; linarith [Int.lt_floor_add_one (x/2)]
  have hperiod : (2 : ℂ)*(n : ℂ) ∈ L.lattice := by
    apply PeriodPair.mem_lattice.mpr
    exact ⟨n,0,by simp [L,rhombicPeriodPair,mul_comm]⟩
  have hxr : (r : ℂ)+(2 : ℂ)*(n : ℂ) = (x : ℂ) := by
    dsimp [r]
    push_cast
    ring
  have hrn : (r : ℂ) ∉ L.lattice := by
    intro h
    apply hxn
    rw [← hxr]
    exact L.lattice.add_mem h hperiod
  have hpr : p x = p r := by
    have h := hp.periodic (r : ℂ) (2*(n : ℂ)) hperiod
    rwa [hxr] at h
  have hrz : p r 2 = 0 := by rw [← hpr]; exact hxz
  have hrne : r ≠ 0 := by
    intro he
    apply hrn
    rw [he]
    simp
  have hr1 : r ≠ 1 := by
    intro he
    apply hp.height_zero_not_two_torsion hrn hrz
    simpa [he,L,rhombicPeriodPair] using L.ω₁_mem_lattice
  have hrpos : 0 < r := lt_of_le_of_ne hr0 hrne.symm
  by_cases hrlt : r < 1
  · exact ⟨r,⟨hrpos,hrlt⟩,hrz⟩
  · have hrgt : 1 < r := lt_of_le_of_ne (le_of_not_gt hrlt) hr1.symm
    refine ⟨2-r,⟨by linarith,by linarith⟩,?_⟩
    have h2 : (2 : ℂ) ∈ L.lattice := L.ω₁_mem_lattice
    have h := congrFun (hp.periodic (-(r : ℂ)) 2 h2) 2
    have he : -(r : ℂ)+2 = ((2-r : ℝ) : ℂ) := by push_cast; ring
    rw [he] at h
    have hn := congrFun (hp.neg (r : ℂ) hrn) 2
    change p (-(r : ℂ)) 2 = p r 2 at hn
    exact h.trans (hn.trans hrz)

/-- A real zero in the normalized interval is a conclusion of nullity,
regularity, both reflections and the sole double-pole height form. -/
theorem symmetric_height_normalized_root_and_simple {t : ℝ} (ht : 0 < t)
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential (rhombicPeriodPair t ht) p)
    {K u : ℂ} (hK : K ≠ 0)
    (hheight : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      p z 2 = K*((rhombicPeriodPair t ht).weierstrassP z-u)) :
    ∃ a : ℝ, a ∈ Ioo (0 : ℝ) 1 ∧ (rhombicPeriodPair t ht).weierstrassP a = u ∧
      (rhombicPeriodPair t ht).derivWeierstrassP a ≠ 0 := by
  obtain ⟨a,ha,haz⟩ := symmetric_height_has_normalized_real_zero ht hp hK hheight
  have han := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have hval : (rhombicPeriodPair t ht).weierstrassP a = u := by
    rw [hheight a han] at haz
    exact sub_eq_zero.mp ((mul_eq_zero.mp haz).resolve_left hK)
  refine ⟨a,ha,hval,?_⟩
  exact (rhombic_weierstrassP_critical_iff_of_pos ht ht han).not.mpr
    (hp.height_zero_not_two_torsion han haz)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.symmetric_height_normalized_root_and_simple
