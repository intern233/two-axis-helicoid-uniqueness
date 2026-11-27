import TwoAxisHelicoid.PdfNegativePrimalSampling

namespace TwoAxisHelicoid.PdfVertical
open Complex Set

def boundedNegativeEdgeCheck (M : ℕ) (T : Grid) (p : PrimalThetaParameters) (i : ℕ) (flag : Bool) : Prop :=
  let y : ℚ := if flag then 3/16 else -3/16
  let b := primalStripOutput T p (-1+(i:ℚ)/16) (-1+((i:ℚ)+1)/16) y y
  b.ok=true ∧ b.mag≤(M:ℤ)*Grid.denom

instance (M : ℕ) (T : Grid) (p : PrimalThetaParameters) (i : ℕ) (flag : Bool) :
    Decidable (boundedNegativeEdgeCheck M T p i flag) := by unfold boundedNegativeEdgeCheck;infer_instance

theorem bounded_negative_strip_of_grid {M : ℕ} {t a : ℝ} {T : Grid} {p : PrimalThetaParameters}
    (ts : T.Contains t) (ps : p.Sound t a) (ht : 17/20≤t)
    (checked : ∀ i : Fin 16, ∀ flag, boundedNegativeEdgeCheck M T p i flag) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+I*((t/2:ℝ):ℂ))‖≤(M:ℝ) := by
  intro z x y
  obtain ⟨i,ilo,ihi⟩ := closed_uniform_cell (N:=16) (by decide) (by norm_num : (-1:ℝ)<0) x
  norm_num only [sub_neg_eq_add,zero_add,one_mul,Nat.cast_ofNat] at ilo ihi
  obtain ⟨flag,he⟩ : ∃ flag : Bool, z.im=(((if flag then 3/16 else -3/16 : ℚ)):ℝ) := by
    by_cases pos : 0≤z.im
    · refine ⟨true,?_⟩
      rw [abs_of_nonneg pos] at y
      simpa only [ite_true,Rat.cast_div,Rat.cast_ofNat] using y
    · refine ⟨false,?_⟩
      rw [abs_of_neg (lt_of_not_ge pos)] at y
      norm_num
      linarith
  obtain ⟨ok,mag⟩ := checked i flag
  have val := primalStripOutput_contains ts ps ht (z:=z) (xl:=-1+(i:ℚ)/16) (xu:=-1+((i:ℚ)+1)/16)
    (yl:=if flag then 3/16 else -3/16) (yu:=if flag then 3/16 else -3/16)
    (by push_cast;exact ⟨ilo,ihi⟩) ⟨he.ge,he.le⟩
  apply (CGrid.norm_le_mag val ok).trans
  rw [Grid.value,div_le_iff₀ Grid.real_denom_pos]
  exact_mod_cast mag

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.bounded_negative_strip_of_grid
