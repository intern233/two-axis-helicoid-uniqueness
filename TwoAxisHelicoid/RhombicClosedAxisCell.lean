import TwoAxisHelicoid.RhombicAxisRectangles
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Algebra.Module.LocallyConvex

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- The closed rectangle between the marked axes. Its southeast and
northwest vertices represent the single puncture. -/
def closedRhombicAxisCell (t : ℝ) : Set ℂ :=
  re ⁻¹' Icc (-1:ℝ) 0 ∩ im ⁻¹' Icc (0:ℝ) t

def regularClosedRhombicAxisCell (t : ℝ) : Set ℂ :=
  closedRhombicAxisCell t ∩ (fun w : ℂ => w.im-w.re) ⁻¹' Ioo 0 (t+1)

theorem closedRhombicAxisCell_convex (t : ℝ) : Convex ℝ (closedRhombicAxisCell t) :=
  ((convex_Icc (-1:ℝ) 0).linear_preimage reCLM.toLinearMap).inter ((convex_Icc 0 t).linear_preimage imCLM.toLinearMap)

theorem regularClosedRhombicAxisCell_convex (t : ℝ) : Convex ℝ (regularClosedRhombicAxisCell t) :=
  (closedRhombicAxisCell_convex t).inter ((convex_Ioo (0:ℝ) (t+1)).linear_preimage (imCLM-reCLM).toLinearMap)

theorem closedRhombicAxisCell_lattice_points {t : ℝ} (ht : 0<t) {z : ℂ}
    (hz : z ∈ closedRhombicAxisCell t) :
    z ∈ (rhombicPeriodPair t ht).lattice ↔ z=0 ∨ z=Complex.mk (-1) t := by
  constructor
  · intro mem
    obtain ⟨m,n,hr,hi⟩ := (rhombic_mem_lattice_iff ht z).mp mem
    have nn : (0:ℤ)≤n := by
      exact_mod_cast nonneg_of_mul_nonneg_left (hi ▸ hz.2.1) ht
    have nl : (n:ℤ)≤1 := by
      exact_mod_cast (show (n:ℝ)≤1 by nlinarith [hz.2.2])
    rcases (show n=0 ∨ n=1 by omega) with h | h
    · subst n
      simp only [Int.cast_zero,add_zero,zero_mul] at hr hi
      have ml : (-1:ℤ)<m := by exact_mod_cast (show (-1:ℝ)<m by linarith [hz.1.1])
      have mu : m≤(0:ℤ) := by exact_mod_cast (show (m:ℝ)≤0 by linarith [hz.1.2])
      have hm : m=0 := by omega
      exact Or.inl (Complex.ext (by simpa [hm] using hr) hi)
    · subst n
      simp only [Int.cast_one,one_mul] at hr hi
      have ml : (-1:ℤ)≤m := by exact_mod_cast (show (-1:ℝ)≤m by linarith [hz.1.1])
      have mu : m<(0:ℤ) := by exact_mod_cast (show (m:ℝ)<0 by linarith [hz.1.2])
      have hm : m= -1 := by omega
      exact Or.inr (Complex.ext (by rw [hm] at hr; norm_num at hr; exact hr) hi)
  · rintro (rfl | rfl)
    · exact (rhombicPeriodPair t ht).lattice.zero_mem
    · exact (rhombic_mem_lattice_iff ht _).mpr ⟨-1,1,by norm_num,by simp⟩

theorem regularClosedRhombicAxisCell_iff {t : ℝ} (ht : 0<t) (z : ℂ) :
    z ∈ regularClosedRhombicAxisCell t ↔ z ∈ closedRhombicAxisCell t ∧ z ∉ (rhombicPeriodPair t ht).lattice := by
  constructor
  · rintro ⟨cell,lo,hi⟩
    refine ⟨cell,fun h => ?_⟩
    rcases (closedRhombicAxisCell_lattice_points ht cell).mp h with rfl | rfl
    · norm_num at lo
    · change t-(-1)<t+1 at hi
      linarith
  · rintro ⟨cell,hn⟩
    refine ⟨cell,?_,?_⟩
    · change 0<z.im-z.re
      by_contra! h
      have zero : z=0 := Complex.ext (by change z.re=0; linarith [cell.1.2,cell.2.1]) (by change z.im=0; linarith [cell.1.2,cell.2.1])
      exact hn ((closedRhombicAxisCell_lattice_points ht cell).mpr (Or.inl zero))
    · change z.im-z.re<t+1
      by_contra! h
      have far : z=Complex.mk (-1) t := Complex.ext (by change z.re= -1; linarith [cell.1.1,cell.2.2]) (by change z.im=t; linarith [cell.1.1,cell.2.2])
      exact hn ((closedRhombicAxisCell_lattice_points ht cell).mpr (Or.inr far))

/-- Affine parametrization by the compact unit square and its continuous
clamped inverse, also defined outside the rectangle. -/
def rhombicCellPoint (t : ℝ) (p : unitInterval × unitInterval) : ℂ :=
  ⟨(p.1:ℝ)-1,t*(p.2:ℝ)⟩

noncomputable def rhombicCellClamp (t : ℝ) (z : ℂ) : unitInterval × unitInterval :=
  (Set.projIcc 0 1 zero_le_one (z.re+1),Set.projIcc 0 1 zero_le_one (z.im/t))

theorem continuous_rhombicCellPoint (t : ℝ) : Continuous (rhombicCellPoint t) :=
  equivRealProdCLM.symm.continuous.comp (((continuous_subtype_val.comp continuous_fst).sub continuous_const).prodMk
    (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))

theorem continuous_rhombicCellClamp (t : ℝ) : Continuous (rhombicCellClamp t) :=
  (continuous_projIcc.comp (continuous_re.add continuous_const)).prodMk (continuous_projIcc.comp (continuous_im.div_const t))

theorem rhombicCellPoint_mem {t : ℝ} (ht : 0<t) (p : unitInterval × unitInterval) :
    rhombicCellPoint t p ∈ closedRhombicAxisCell t := by
  refine ⟨⟨?_,?_⟩,⟨mul_nonneg ht.le p.2.2.1,?_⟩⟩
  · change -1≤(p.1:ℝ)-1; linarith [p.1.2.1]
  · change (p.1:ℝ)-1≤0; linarith [p.1.2.2]
  · exact mul_le_of_le_one_right ht.le p.2.2.2

theorem rhombicCellPoint_clamp {t : ℝ} (ht : 0<t) {z : ℂ} (hz : z ∈ closedRhombicAxisCell t) :
    rhombicCellPoint t (rhombicCellClamp t z)=z := by
  have x : z.re+1 ∈ Icc (0:ℝ) 1 := ⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩
  have y : z.im/t ∈ Icc (0:ℝ) 1 := ⟨div_nonneg hz.2.1 ht.le,(div_le_one ht).mpr hz.2.2⟩
  apply Complex.ext
  · change (Set.projIcc 0 1 zero_le_one (z.re+1):ℝ)-1=z.re
    rw [Set.projIcc_of_mem _ x]; simp
  · change t*(Set.projIcc 0 1 zero_le_one (z.im/t):ℝ)=z.im
    rw [Set.projIcc_of_mem _ y]; dsimp; field_simp

theorem rhombicCellClamp_point {t : ℝ} (ht : 0<t) (q : unitInterval × unitInterval) :
    rhombicCellClamp t (rhombicCellPoint t q)=q := by
  have h := rhombicCellPoint_clamp ht (rhombicCellPoint_mem ht q)
  have inj : Function.Injective (rhombicCellPoint t) := by
    rintro ⟨a,b⟩ ⟨c,d⟩ e
    apply Prod.ext
    · apply Subtype.ext
      have h : (a:ℝ)-1=(c:ℝ)-1 := congrArg Complex.re e
      linarith
    · apply Subtype.ext
      exact mul_left_cancel₀ ht.ne' (congrArg Complex.im e)
  exact inj h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regularClosedRhombicAxisCell_iff
#print axioms TwoAxisHelicoid.rhombicCellPoint_clamp
