import TwoAxisHelicoid.CertifiedWeierstrassSeparation
import TwoAxisHelicoid.ComplexBallChecked

namespace TwoAxisHelicoid
open Complex ComplexBall Set Metric

/-- A bound on one complex coefficient controls the error of the real
spatial displacement along a straight parameter segment. -/
theorem weierstrass_coordinate_chord_error {X : ℂ → Fin 3 → ℝ} {p : ℂ → Fin 3 → ℂ} {U : Set ℂ}
    (conv : Convex ℝ U) (der : ∀ w∈U, HasFDerivAt X (nullRealDerivative (p w)) w)
    (j : Fin 3) (b : ComplexBall) (contains : ∀ w∈U, b.Contains (p w j))
    {x y : ℂ} (hx : x∈U) (hy : y∈U) :
    |X y j-X x j-((y-x)*b.center.val).re|≤ (b.radius:ℝ)*‖y-x‖ := by
  let pr := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j)
  let D := fun w => pr.comp (nullRealDerivative (p w))
  let T := realCoefficientDerivative b.center.val
  have hd (w : ℂ) (hw : w∈U) : HasFDerivWithinAt (fun z => X z j) (D w) U w :=
    (pr.hasFDerivAt.comp w (der w hw)).hasFDerivWithinAt
  have br : 0≤(b.radius:ℝ) := by exact_mod_cast radius_nonneg (contains x hx)
  have bound (w : ℂ) (hw : w∈U) : ‖D w-T‖≤(b.radius:ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ br
    intro v
    change ‖(v*p w j).re-(v*b.center.val).re‖≤(b.radius:ℝ)*‖v‖
    rw [← sub_re,← mul_sub,Real.norm_eq_abs]
    exact (abs_re_le_norm _).trans (by rw [norm_mul,mul_comm (b.radius:ℝ)]; exact mul_le_mul_of_nonneg_left (contains w hw) (norm_nonneg _))
  exact conv.norm_image_sub_le_of_norm_hasFDerivWithin_le' hd bound hx hy

/-- Summing certified edge errors bounds the displacement along an
arbitrary polygon, with each edge using its own coefficient enclosure. -/
theorem spatial_polygon_displacement {X : ℂ → Fin 3 → ℝ} (j : Fin 3) (n : ℕ) (z : ℕ → ℂ)
    (v e : ℕ → ℝ) (edges : ∀ i<n, |X (z (i+1)) j-X (z i) j-v i|≤e i) :
    |X (z n) j-X (z 0) j-∑ i∈Finset.range n, v i|≤∑ i∈Finset.range n, e i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have prev := ih (fun i h => edges i (Nat.lt_succ_of_lt h))
    have last := edges n (Nat.lt_succ_self n)
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    calc
      _=|(X (z n) j-X (z 0) j-∑ i∈Finset.range n, v i)+(X (z (n+1)) j-X (z n) j-v n)| := by congr 1; ring
      _≤_ := (abs_add_le _ _).trans (add_le_add prev last)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.weierstrass_coordinate_chord_error
#print axioms TwoAxisHelicoid.spatial_polygon_displacement
