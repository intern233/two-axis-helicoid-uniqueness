import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox

namespace TwoAxisHelicoid.PdfVertical
open Complex Set

def negativeEdgeCheck (T : Grid) (p : PrimalThetaParameters) (i : ℕ) (flag : Bool) : Prop :=
  let y : ℚ := if flag then 3/16 else -3/16
  let b := primalStripOutput T p (-1+(i:ℚ)/16) (-1+((i:ℚ)+1)/16) y y
  b.ok=true ∧ b.mag≤(10:ℤ)^7*Grid.denom

instance (T : Grid) (p : PrimalThetaParameters) (i : ℕ) (flag : Bool) :
    Decidable (negativeEdgeCheck T p i flag) := by unfold negativeEdgeCheck;infer_instance

theorem negative_primal_strip_of_grid {t a : ℝ} {T : Grid} {p : PrimalThetaParameters}
    (ts : T.Contains t) (ps : p.Sound t a) (ht : 17/20≤t)
    (checked : ∀ i : Fin 16, ∀ flag, negativeEdgeCheck T p i flag) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+I*((t/2:ℝ):ℂ))‖≤10^7 := by
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

theorem negative_24_point_error {t a : ℝ} (ht : 9/10≤t)
    (bd : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+I*((t/2:ℝ):ℂ))‖≤10^7) :
    |(1/24:ℝ)*(∑ k∈Finset.range 24,(thetaA t a (((-1+(k:ℝ)/24:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re)
      -thetaHorizontalPeriod t a|≤1/1000 := by
  have sample := periodic_theta_sample_error (N:=24) (by decide) (s:=3/16) (by norm_num) (by linarith) bd
  apply sample.trans
  let r := Real.exp (-(2*Real.pi*((24:ℝ)*(3/16))))
  have exp27 : (27/10:ℝ)^27≤Real.exp 27 := by
    rw [show (27:ℝ)=(27:ℕ)*(1:ℝ) by norm_num,Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have upper : r≤1/30000000000 := by
    dsimp only [r]
    simp only [Real.exp_neg,one_div]
    apply inv_anti₀ (by norm_num)
    exact ((by norm_num : (30000000000:ℝ)≤(27/10)^27).trans exp27).trans
      (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three]))
  change 2*((10:ℝ)^7*r/(1-r))≤_
  have pos : 0<1-r := by linarith
  rw [← mul_div_assoc,div_le_iff₀ pos]
  linarith

def negativeSampleCheck (T : Grid) (p : PrimalThetaParameters) (k : ℕ) (l u : ℚ) : Bool :=
  let x : ℚ := -1+(k:ℚ)/24
  containedInReported (primalStripOutput T p x x 0 0).re l u

theorem negative_sample_check_sound {T : Grid} {p : PrimalThetaParameters} {t a : ℝ} (ts : T.Contains t)
    (ps : p.Sound t a) (ht : 17/20≤t) (k : ℕ) {l u : ℚ} (ok : negativeSampleCheck T p k l u=true) :
    (l:ℝ)≤(thetaA t a (((-1+(k:ℝ)/24:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re ∧
      (thetaA t a (((-1+(k:ℝ)/24:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re≤(u:ℝ) := by
  let x : ℚ := -1+(k:ℚ)/24
  have eq : (x:ℝ)= -1+(k:ℝ)/24 := by simp [x]
  have val := primalStripOutput_contains ts ps ht (z:=((x:ℝ):ℂ)) (xl:=x) (xu:=x) (yl:=0) (yu:=0)
    ⟨le_rfl,le_rfl⟩ (by simp)
  simpa only [eq] using containedInReported_sound val.1 ok

theorem negative_original_rectangle_bounds {T : Grid} {p : PrimalThetaParameters} {t a : ℝ}
    (ts : T.Contains t) (ps : p.Sound t a) (ht : 9/10≤t)
    (edge : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+I*((t/2:ℝ):ℂ))‖≤10^7)
    (l u : ℕ → ℚ) (lo hi : ℚ) (checked : ∀ i : Fin 24, negativeSampleCheck T p i (l i) (u i)=true)
    (small : lo≤(∑ k∈Finset.range 24,l k)/24-1/1000 ∧ (∑ k∈Finset.range 24,u k)/24+1/1000≤hi) :
    (lo:ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(hi:ℝ) := by
  let f := fun k : ℕ => (thetaA t a (((-1+(k:ℝ)/24:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re
  have errors := abs_le.mp (negative_24_point_error ht edge)
  have all (k : ℕ) (h : k∈Finset.range 24) : (l k:ℝ)≤f k ∧ f k≤(u k:ℝ) :=
    negative_sample_check_sound ts ps (by linarith) k (checked ⟨k,Finset.mem_range.mp h⟩)
  have L : (∑ k∈Finset.range 24,(l k:ℝ))≤∑ k∈Finset.range 24,f k :=
    Finset.sum_le_sum (fun k hk => (all k hk).1)
  have U : (∑ k∈Finset.range 24,f k)≤∑ k∈Finset.range 24,(u k:ℝ) :=
    Finset.sum_le_sum (fun k hk => (all k hk).2)
  have lr : (lo:ℝ)≤(∑ k∈Finset.range 24,(l k:ℝ))/24-1/1000 := by
    have h := (Rat.cast_le (K:=ℝ)).mpr small.1
    push_cast at h
    exact h
  have ur : (∑ k∈Finset.range 24,(u k:ℝ))/24+1/1000≤(hi:ℝ) := by
    have h := (Rat.cast_le (K:=ℝ)).mpr small.2
    push_cast at h
    exact h
  change -(1/1000:ℝ)≤(1/24:ℝ)*(∑ k∈Finset.range 24,f k)-thetaHorizontalPeriod t a ∧ _ at errors
  constructor <;> linarith [errors.1,errors.2]

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.negative_original_rectangle_bounds
