import TwoAxisHelicoid.CompactQuarticArea

namespace TwoAxisHelicoid
open Set MeasureTheory

/-- A regular chart only supplies a strictly positive metric coefficient.
Its positive minimum on the support suffices to differentiate the
quartic area integral twice. -/
theorem positive_compact_quartic_area_second_derivative
    {g A B C : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hg : ContinuousOn g K) (hA : ContinuousOn A K) (hB : ContinuousOn B K)
    (hC : ContinuousOn C K) (pos : ∀ p ∈ K, 0 < g p) :
    HasDerivAt (deriv (fun s : ℝ => ∫ p in K,
      Real.sqrt (areaQuartic (g p) (A p) (B p) (C p) s))) (∫ p in K, A p/g p) 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hn
  · simpa using (hasDerivAt_const (0:ℝ) (0:ℝ))
  obtain ⟨x,hx,minimum⟩ := hK.exists_isMinOn hn hg
  let d := g x
  have hd : 0 < d := pos x hx
  have lower (p) (hp : p∈K) : 1 ≤ g p/d := (one_le_div hd).mpr (minimum hp)
  let Q := fun (p : ℝ × ℝ) (s : ℝ) => areaQuartic (g p/d) (A p/d^2) (B p/d^2) (C p/d^2) s
  have h := compact_quartic_area_integral_second_derivative hK (hg.div_const d)
    (hA.div_const (d^2)) (hB.div_const (d^2)) (hC.div_const (d^2)) lower
  have factor (p : ℝ × ℝ) (s : ℝ) :
      Real.sqrt (areaQuartic (g p) (A p) (B p) (C p) s)=d*Real.sqrt (Q p s) := by
    have eq : areaQuartic (g p) (A p) (B p) (C p) s=d^2*Q p s := by
      dsimp [Q,areaQuartic]
      field_simp [hd.ne']
    rw [eq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hd.le]
  have area : (fun s : ℝ => ∫ p in K, Real.sqrt (areaQuartic (g p) (A p) (B p) (C p) s))=
      fun s => d*(∫ p in K, Real.sqrt (Q p s)) := by
    funext s
    simp only [factor,integral_const_mul]
  have coeff : d*(∫ p in K, (A p/d^2)/(g p/d))=∫ p in K, A p/g p := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun hK.measurableSet
    intro p hp
    field_simp [hd.ne',(pos p hp).ne']
  rw [area,deriv_const_mul_field',← coeff]
  exact h.const_mul d

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positive_compact_quartic_area_second_derivative
