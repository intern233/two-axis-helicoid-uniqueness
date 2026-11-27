import TwoAxisHelicoid.PdfPrimalGridSampling
import TwoAxisHelicoid.PdfVerticalRowSound

namespace TwoAxisHelicoid.PdfVertical
open Complex Set

def primalSampleCheck (T : Grid) (p : PrimalThetaParameters) (k : ℕ) (u : ℚ) : Bool :=
  let x : ℚ := -1+(k:ℚ)/8
  containedInReported (primalStripOutput T p x x 0 0).re (-10000) u

theorem primalSampleCheck_sound {T : Grid} {p : PrimalThetaParameters} {t a : ℝ}
    (ts : T.Contains t) (ps : p.Sound t a) (ht : 17/20≤t) (k : ℕ) {u : ℚ}
    (ok : primalSampleCheck T p k u=true) :
    (thetaA t a (((-1+(k:ℝ)/8:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re≤(u:ℝ) := by
  let x : ℚ := -1+(k:ℚ)/8
  have eq : (x:ℝ)= -1+(k:ℝ)/8 := by push_cast [x];rfl
  have val := primalStripOutput_contains ts ps ht (z:=((x:ℝ):ℂ))
    (xl:=x) (xu:=x) (yl:=0) (yu:=0) ⟨le_rfl,le_rfl⟩ (by simp)
  simpa only [eq] using (containedInReported_sound val.1 ok).2

/-- A subrectangle supplies only eight scalar grid comparisons. The
holomorphic error uses the same two edge bounds across the ten source boxes. -/
theorem primal_eight_point_upper {T : Grid} {p : PrimalThetaParameters} {t a : ℝ}
    (ts : T.Contains t) (ps : p.Sound t a) (ht : 17/20≤t)
    (edge : ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/8 →
      ‖thetaA t a (z+I*((t/2:ℝ):ℂ))‖≤4096)
    (upper : ℕ → ℚ) (cap : ℚ) (checked : ∀ i : Fin 8, primalSampleCheck T p i (upper i)=true)
    (small : (∑ k∈Finset.range 8,upper k)/8+1/1000≤cap) :
    thetaHorizontalPeriod t a≤(cap:ℝ) := by
  have res := periodic_theta_sample_error (N:=8) (by decide) (s:=3/8) (by norm_num)
    (by linarith : 2*(3/8)<t) edge
  have err := (abs_le.mp (res.trans right_sample_error_small)).1
  have samples : (∑ k∈Finset.range 8,
      (thetaA t a (((-1+(k:ℝ)/8:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re)≤∑ k∈Finset.range 8, (upper k:ℝ) := by
    exact Finset.sum_le_sum (fun k hk => primalSampleCheck_sound ts ps ht k (checked ⟨k,Finset.mem_range.mp hk⟩))
  have capReal : (∑ k∈Finset.range 8,(upper k:ℝ))/8+1/1000≤(cap:ℝ) := by
    have h := (Rat.cast_le (K:=ℝ)).mpr small
    push_cast at h
    exact h
  linarith

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.primal_eight_point_upper
