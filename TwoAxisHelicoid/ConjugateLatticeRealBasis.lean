import TwoAxisHelicoid.PeriodTorusConjugation
import Mathlib.GroupTheory.Archimedean

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate Topology

def latticeRealSubgroup (L : PeriodPair) : AddSubgroup ℝ where
  carrier := {x | (x : ℂ) ∈ L.lattice}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simpa using L.lattice.add_mem ha hb
  neg_mem' := by intro a ha; simpa using L.lattice.neg_mem ha

def latticeImaginarySubgroup (L : PeriodPair) : AddSubgroup ℝ where
  carrier := {y | ∃ z ∈ L.lattice, z.im = y}
  zero_mem' := ⟨0,by simp,by simp⟩
  add_mem' := by
    rintro a b ⟨z,hz,rfl⟩ ⟨w,hw,rfl⟩
    exact ⟨z+w,L.lattice.add_mem hz hw,Complex.add_im z w⟩
  neg_mem' := by
    rintro a ⟨z,hz,rfl⟩
    exact ⟨-z,L.lattice.neg_mem hz,Complex.neg_im z⟩

theorem lattice_norm_isolated_zero (L : PeriodPair) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ L.lattice, ‖z‖ < ε → z = 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  refine ⟨ε,hε,?_⟩
  intro z hz hn
  have h := hball (show z ∈ Metric.ball 0 ε by simpa using hn)
  by_contra hz0
  exact h ⟨hz,hz0⟩

theorem lattice_exists_nonzero_real_part (L : PeriodPair) :
    ∃ z ∈ L.lattice, z.re ≠ 0 := by
  by_contra! h
  have hrep := congrArg Complex.re (L.basis.sum_repr (1 : ℂ))
  simp [Fin.sum_univ_two,Complex.real_smul,Complex.mul_re,
    h L.ω₁ L.ω₁_mem_lattice,h L.ω₂ L.ω₂_mem_lattice] at hrep

theorem lattice_exists_nonzero_imaginary_part (L : PeriodPair) :
    ∃ z ∈ L.lattice, z.im ≠ 0 := by
  by_contra! h
  have hrep := congrArg Complex.im (L.basis.sum_repr I)
  simp [Fin.sum_univ_two,Complex.real_smul,Complex.mul_im,
    h L.ω₁ L.ω₁_mem_lattice,h L.ω₂ L.ω₂_mem_lattice] at hrep

theorem conjugation_lattice_real_subgroup_nontrivial (L : PeriodPair)
    (hL : ConjugationInvariantLattice L) : latticeRealSubgroup L ≠ ⊥ := by
  obtain ⟨z,hz,hr⟩ := lattice_exists_nonzero_real_part L
  have hm : 2*z.re ∈ latticeRealSubgroup L := by
    change ((2*z.re : ℝ) : ℂ) ∈ L.lattice
    have he : ((2*z.re : ℝ) : ℂ) = z+conj z := by
      apply Complex.ext <;> simp
      ring
    rw [he]
    exact L.lattice.add_mem hz (hL z hz)
  intro hbot
  rw [hbot] at hm
  have he : 2*z.re = 0 := hm
  exact hr (by linarith)

theorem lattice_imaginary_subgroup_nontrivial (L : PeriodPair) :
    latticeImaginarySubgroup L ≠ ⊥ := by
  obtain ⟨z,hz,hi⟩ := lattice_exists_nonzero_imaginary_part L
  have hm : z.im ∈ latticeImaginarySubgroup L := ⟨z,hz,rfl⟩
  intro hbot
  rw [hbot] at hm
  exact hi hm

theorem conjugation_lattice_has_real_generator (L : PeriodPair)
    (hL : ConjugationInvariantLattice L) :
    ∃ r : ℝ, 0 < r ∧ AddSubgroup.zmultiples r = latticeRealSubgroup L := by
  obtain ⟨ε,hε,hgap⟩ := lattice_norm_isolated_zero L
  have hd : Disjoint (latticeRealSubgroup L : Set ℝ) (Ioo 0 ε) := by
    apply Set.disjoint_left.mpr
    intro x hx hxi
    have hz := hgap (x : ℂ) hx (by simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxi.1] using hxi.2)
    have hx0 := congrArg Complex.re hz
    simp only [Complex.ofReal_re,Complex.zero_re] at hx0
    linarith [hxi.1]
  obtain ⟨r,hr⟩ := AddSubgroup.exists_isLeast_pos
    (conjugation_lattice_real_subgroup_nontrivial L hL) hε hd
  exact ⟨r,hr.1.2,AddSubgroup.zmultiples_eq_of_isLeast_mem_and_pos hr⟩

theorem conjugation_lattice_has_imaginary_generator (L : PeriodPair)
    (hL : ConjugationInvariantLattice L) :
    ∃ t : ℝ, 0 < t ∧ AddSubgroup.zmultiples t = latticeImaginarySubgroup L := by
  obtain ⟨ε,hε,hgap⟩ := lattice_norm_isolated_zero L
  have hd : Disjoint (latticeImaginarySubgroup L : Set ℝ) (Ioo 0 (ε/2)) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨z,hz,rfl⟩ hy
    have he : z-conj z = I*(2*z.im) := by
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
      ring
    have hn : ‖z-conj z‖ < ε := by
      rw [he,norm_mul,Complex.norm_I,one_mul]
      simpa [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy.1] using
        (show 2*z.im < ε by linarith [hy.2])
    have hzero := hgap (z-conj z) (L.lattice.sub_mem hz (hL z hz)) hn
    have hi := congrArg Complex.im hzero
    simp only [Complex.sub_im,Complex.conj_im,Complex.zero_im] at hi
    linarith [hy.1]
  obtain ⟨t,ht⟩ := AddSubgroup.exists_isLeast_pos
    (lattice_imaginary_subgroup_nontrivial L) (by linarith : 0 < ε/2) hd
  exact ⟨t,ht.1.2,AddSubgroup.zmultiples_eq_of_isLeast_mem_and_pos ht⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.conjugation_lattice_has_real_generator
#print axioms TwoAxisHelicoid.conjugation_lattice_has_imaginary_generator
