import TwoAxisHelicoid.PdfHeatGridKernel
import TwoAxisHelicoid.PdfHeatSampling
import TwoAxisHelicoid.PdfVerticalRowSound

namespace TwoAxisHelicoid.PdfVertical
open Complex Set

noncomputable def reportedHeatPeriod (t a : ℝ) : ℝ :=
  (1/2:ℝ)*(∫ x : ℝ in (-1)..1, pdfHeatKernel t a (-(thetaGt t a).re/(thetaGa t a).re)
    ((x:ℂ)+I*((t/2:ℝ):ℂ))).re

theorem reportedHeatPeriod_branch {t : ℝ} (ht : t∈Ioo (0:ℝ) ellipticVerticalUpper) :
    reportedHeatPeriod t (verticalA t)=deriv actualPeriodAlong t :=
  (original_pdf_heat_derivative_formula ht).symm

def heatEdgeCheck (T : Grid) (p : HeatGridParameters) (i : ℕ) (flag : Bool) : Prop :=
  let y : ℚ := if flag then 3/16 else -3/16
  let b := heatGridOutput T p (-1+(i:ℚ)/32) (-1+((i:ℚ)+1)/32) y y
  b.ok=true ∧ b.mag≤(10:ℤ)^7*Grid.denom

instance (T : Grid) (p : HeatGridParameters) (i : ℕ) (flag : Bool) :
    Decidable (heatEdgeCheck T p i flag) := by unfold heatEdgeCheck;infer_instance

theorem heat_grid_strip_bound {t a : ℝ} {T : Grid} {p : HeatGridParameters}
    (ts : T.Contains t) (ps : p.Sound t a) (ht : 17/20≤t)
    (checked : ∀ i : Fin 64, ∀ flag, heatEdgeCheck T p i flag) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 1 → |z.im|=3/16 →
      ‖pdfHeatKernel t a (-(thetaGt t a).re/(thetaGa t a).re) (z+I*((t/2:ℝ):ℂ))‖≤10^7 := by
  intro z x y
  obtain ⟨i,left,right⟩ := closed_uniform_cell (N:=64) (by decide) (by norm_num : (-1:ℝ)<1) x
  have ilo : -1+(i:ℝ)/32≤z.re := by linarith only [left]
  have ihi : z.re≤ -1+((i:ℝ)+1)/32 := by linarith only [right]
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
  have val := heatGridOutput_contains ts ps ht (z:=z) (xl:=-1+(i:ℚ)/32) (xu:=-1+((i:ℚ)+1)/32)
    (yl:=if flag then 3/16 else -3/16) (yu:=if flag then 3/16 else -3/16)
    (by push_cast;exact ⟨ilo,ihi⟩) ⟨he.ge,he.le⟩
  apply (CGrid.norm_le_mag val ok).trans
  rw [Grid.value,div_le_iff₀ Grid.real_denom_pos]
  exact_mod_cast mag

def heatSampleCheck (T : Grid) (p : HeatGridParameters) (k : ℕ) (u : ℚ) : Bool :=
  let x : ℚ := 2*((k:ℚ)/32)-1
  containedInReported (heatGridOutput T p x x 0 0).re (-10000) u

theorem heatSampleCheck_sound {T : Grid} {p : HeatGridParameters} {t a : ℝ}
    (ts : T.Contains t) (ps : p.Sound t a) (ht : 17/20≤t) (k : ℕ) {u : ℚ}
    (ok : heatSampleCheck T p k u=true) :
    (pdfHeatKernel t a (-(thetaGt t a).re/(thetaGa t a).re)
      (((2*((k:ℝ)/32)-1:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re≤(u:ℝ) := by
  let x : ℚ := 2*((k:ℚ)/32)-1
  have eq : (x:ℝ)=2*((k:ℝ)/32)-1 := by simp [x]
  have val := heatGridOutput_contains ts ps ht (z:=((x:ℝ):ℂ))
    (xl:=x) (xu:=x) (yl:=0) (yu:=0) ⟨le_rfl,le_rfl⟩ (by simp)
  simpa only [eq] using (containedInReported_sound val.1 ok).2

theorem heat_32_point_upper {T : Grid} {p : HeatGridParameters} {t a : ℝ}
    (ts : T.Contains t) (ps : p.Sound t a) (ht : 17/20≤t)
    (edge : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 1 → |z.im|=3/16 →
      ‖pdfHeatKernel t a (-(thetaGt t a).re/(thetaGa t a).re) (z+I*((t/2:ℝ):ℂ))‖≤10^7)
    (upper : ℕ → ℚ) (cap : ℚ) (checked : ∀ i : Fin 32, heatSampleCheck T p i (upper i)=true)
    (small : (∑ k∈Finset.range 32,upper k)/32+1/5≤cap) :
    reportedHeatPeriod t a≤(cap:ℝ) := by
  have err := (abs_le.mp (pdf_heat_32_point_period_error ht edge)).1
  have samples : (∑ k∈Finset.range 32, (pdfHeatKernel t a (-(thetaGt t a).re/(thetaGa t a).re)
    (((2*((k:ℝ)/32)-1:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re)≤∑ k∈Finset.range 32,(upper k:ℝ) :=
    Finset.sum_le_sum (fun k hk => heatSampleCheck_sound ts ps ht k (checked ⟨k,Finset.mem_range.mp hk⟩))
  have capReal : (∑ k∈Finset.range 32,(upper k:ℝ))/32+1/5≤(cap:ℝ) := by
    have h := (Rat.cast_le (K:=ℝ)).mpr small
    push_cast at h
    exact h
  unfold reportedHeatPeriod
  linarith

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heat_grid_strip_bound
#print axioms TwoAxisHelicoid.PdfVertical.heat_32_point_upper
