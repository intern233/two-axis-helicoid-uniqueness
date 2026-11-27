import TwoAxisHelicoid.RhombicWeightedHeight
import Mathlib.Topology.Order.IntermediateValue

namespace TwoAxisHelicoid
open Set Complex Topology
open scoped ComplexConjugate

private theorem weak_sign_on_interval {h : unitInterval → ℝ} (ch : Continuous h) (h₀ : h 0=0) (h₁ : h 1=0)
    (nonzero : ∀ y∈Ioo (0:unitInterval) 1, h y≠0) {c : unitInterval} (mid : c∈Ioo (0:unitInterval) 1)
    (pos : 0<h c) (x : unitInterval) : 0≤h x := by
  by_cases zero : x=0
  · simp [zero,h₀]
  by_cases one : x=1
  · simp [one,h₁]
  have xm : x∈Ioo (0:unitInterval) 1 := ⟨lt_of_le_of_ne bot_le (Ne.symm zero),lt_of_le_of_ne le_top one⟩
  by_contra! neg
  obtain ⟨u,hu,eq⟩ := isPreconnected_Ioo.intermediate_value xm mid ch.continuousOn (show (0:ℝ)∈Icc (h x) (h c) from ⟨neg.le,pos.le⟩)
  exact nonzero u hu eq

private theorem height_weak_signs {L R : unitInterval → ℝ} (cL : Continuous L) (cR : Continuous R)
    (l₀ : L 0=0) (l₁ : L 1=0) (r₀ : R 0=0) (r₁ : R 1=0)
    (nz : ∀ y∈Ioo (0:unitInterval) 1, L y≠0 ∧ R y≠0) {a : unitInterval}
    (mid : a∈Ioo (0:unitInterval) 1) (opp : L a= -R a) :
    (∀ y, L y≤0 ∧ 0≤R y) ∨ (∀ y, 0≤L y ∧ R y≤0) := by
  have plus {h : unitInterval → ℝ} (ch : Continuous h) (h0 : h 0=0) (h1 : h 1=0) (no : ∀ y∈Ioo (0:unitInterval) 1, h y≠0)
      (neg : h a<0) (y) : h y≤0 :=
    neg_nonneg.mp (weak_sign_on_interval ch.neg (by simp [h0]) (by simp [h1]) (fun u hu => neg_ne_zero.mpr (no u hu)) mid (neg_pos.mpr neg) y)
  rcases lt_or_gt_of_ne (nz a mid).2 with rn | rp
  · refine Or.inr (fun y => ⟨weak_sign_on_interval cL l₀ l₁ (fun u hu => (nz u hu).1) mid (opp.symm ▸ neg_pos.mpr rn) y,
      plus cR r₀ r₁ (fun u hu => (nz u hu).2) rn y⟩)
  · exact Or.inl (fun y => ⟨plus cL l₀ l₁ (fun u hu => (nz u hu).1) (opp.symm ▸ neg_neg_of_pos rp) y,
      weak_sign_on_interval cR r₀ r₁ (fun u hu => (nz u hu).2) mid rp y⟩)

/-- The true bounded height test has weak opposite signs on the closed
vertical edges, and has no zeros on their relative interiors. The
sign reversal follows from reflection and a marked lattice period. -/
theorem marked_closed_cell_height_signs {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X) (hi : Function.Injective (harmonicTorusImmersion hX)) :
    let H := rhombicWeightedHeight t X ∘ rhombicCellPoint t
    Continuous H ∧ ((∀ y, H (0,y)≤0 ∧ 0≤H (1,y)) ∨ (∀ y, 0≤H (0,y) ∧ H (1,y)≤0)) ∧
      ∀ y : unitInterval, y≠0 → y≠1 → H (0,y)≠0 ∧ H (1,y)≠0 := by
  let L := rhombicPeriodPair t ht
  let H := rhombicWeightedHeight t X ∘ rhombicCellPoint t
  have ch : Continuous H := (rhombicWeightedHeight_continuousOn ht hX).comp_continuous (continuous_rhombicCellPoint t) (rhombicCellPoint_mem ht)
  have nz (y : unitInterval) (hy : y∈Ioo (0:unitInterval) 1) : H (0,y)≠0 ∧ H (1,y)≠0 := by
    exact ⟨(rhombic_middle_avoids_horizontal_axis ht hX hi (0,y) hy).2 (Or.inl rfl),
      (rhombic_middle_avoids_horizontal_axis ht hX hi (1,y) hy).2 (Or.inr rfl)⟩
  have corner (x y : unitInterval) (hy : y=0 ∨ y=1) : H (x,y)=0 := by
    let z := rhombicCellPoint t (x,y)
    have mem := rhombicCellPoint_mem ht (x,y)
    by_cases reg : z∉L.lattice
    · have height : ∃ k : ℤ, z.im=k*t := by
        rcases hy with rfl | rfl
        · exact ⟨0,by simp [z,rhombicCellPoint]⟩
        · exact ⟨1,by simp [z,rhombicCellPoint]⟩
      exact (rhombicWeightedHeight_zero_iff ((regularClosedRhombicAxisCell_iff ht _).mpr ⟨mem,reg⟩) X).mpr
        (((rhombic_physical_axes_preimages ht hX hi reg).2.mpr height).2)
    · have cor := (closedRhombicAxisCell_lattice_points ht mem).mp (not_not.mp reg)
      change rhombicWeightedHeight t X z=0
      rcases cor with e | e <;> change z=_ at e <;> rw [e] <;> simp [rhombicWeightedHeight,rhombicCellWeight]
  let c : unitInterval := ⟨1/2,by norm_num,by norm_num⟩
  have mid : c∈Ioo (0:unitInterval) 1 := ⟨by change (0:ℝ)<1/2; norm_num,by change (1:ℝ)/2<1; norm_num⟩
  let l := rhombicCellPoint t (0,c)
  let r := rhombicCellPoint t (1,c)
  have reg : r∉L.lattice := ((regularClosedRhombicAxisCell_iff ht _).mp (rhombicCell_middle_regular ht (1,c) mid)).2
  have creg : conj r∉L.lattice := fun h => reg (by simpa using rhombic_conj_mem ht h)
  let ω : ℂ := ⟨-1,t⟩
  have period : ω∈L.lattice := (rhombic_mem_lattice_iff ht ω).mpr ⟨-1,1,by norm_num [ω],by simp [ω]⟩
  have pair : conj r+ω=l := by
    apply Complex.ext
    · simp [l,r,ω,c,rhombicCellPoint]
    · simp [l,r,ω,c,rhombicCellPoint]
      ring
  have hand := congrFun (hX.periodic (conj r) creg ω period) 2
  rw [pair,hX.conjugation r reg] at hand
  have hh : X l 2= -X r 2 := hand
  have weight : rhombicCellWeight t l=rhombicCellWeight t r := by
    simp [rhombicCellWeight,l,r,rhombicCellPoint,c]
    ring
  have opp : H (0,c)= -H (1,c) := by
    change rhombicCellWeight t l*(X l 2/(1+|X l 2|))= -(rhombicCellWeight t r*(X r 2/(1+|X r 2|)))
    rw [hh,weight,abs_neg,neg_div,mul_neg]
  refine ⟨ch,height_weak_signs (ch.comp (continuous_const.prodMk continuous_id)) (ch.comp (continuous_const.prodMk continuous_id))
    (corner 0 0 (Or.inl rfl)) (corner 0 1 (Or.inr rfl)) (corner 1 0 (Or.inl rfl)) (corner 1 1 (Or.inr rfl)) nz mid opp,?_⟩
  exact fun y y0 y1 => nz y ⟨lt_of_le_of_ne bot_le (Ne.symm y0),lt_of_le_of_ne le_top y1⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_closed_cell_height_signs
