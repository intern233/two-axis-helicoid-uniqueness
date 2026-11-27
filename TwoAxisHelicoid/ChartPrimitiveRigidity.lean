import TwoAxisHelicoid.ChartRegularConnected
import TwoAxisHelicoid.WeierstrassRotation

namespace TwoAxisHelicoid
open Complex Set Metric
set_option maxHeartbeats 800000

namespace HolomorphicCoefficientDisks
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A function whose actual chart derivatives vanish is constant along each
piecewise coordinate path. No globally defined primitive is assumed. -/
theorem AvoidingPath.eq_of_chart_derivative_zero
    {A : HolomorphicCoefficientDisks M} {U : Set M} {Z : M → E}
    (hZ : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) →
      (chartAt ℂ p).symm z ∈ U →
      HasFDerivAt (fun w : ℂ => Z ((chartAt ℂ p).symm w)) (0 : ℂ →L[ℝ] E) z)
    {x y : M} (c : A.AvoidingPath U x y) : Z y = Z x := by
  induction c with
  | refl => rfl
  | step p x y hx hy hU =>
      have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
          HasDerivAt (fun s : ℝ => Z ((chartAt ℂ p).symm (chartSegment p x y s))) (0 : E) s := by
        have he := (hZ p _ (A.chartSegment_mem p hx hy hs) (hU s hs)).comp_hasDerivAt s
          (AffineMap.hasDerivAt_lineMap (𝕜 := ℝ)
            (a := chartAt ℂ p x) (b := chartAt ℂ p y) (x := s))
        simpa only [Function.comp_def,zero_apply] using! he
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hd s (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs))
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : E)) MeasureTheory.volume 0 1)
      have hz : (0 : E) = Z y-Z x := by
        simpa only [intervalIntegral.integral_zero,chartSegment,AffineMap.lineMap_apply_one,
          AffineMap.lineMap_apply_zero,(chartAt ℂ p).left_inv hx.1,(chartAt ℂ p).left_inv hy.1] using! he
      exact sub_eq_zero.mp hz.symm
  | trans c d hc hd => exact hd.trans hc

theorem constant_of_chart_derivative_zero [PreconnectedSpace M] [Nonempty M]
    (A : HolomorphicCoefficientDisks M) {P : Set M} (hP : P.Finite) {Z : M → E}
    (hZ : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) →
      (chartAt ℂ p).symm z ∉ P →
      HasFDerivAt (fun w : ℂ => Z ((chartAt ℂ p).symm w)) (0 : ℂ →L[ℝ] E) z) :
    ∃ b : E, ∀ x ∉ P, Z x = b := by
  obtain ⟨x,hx⟩ := (finite_compl_dense_complex_charts hP).nonempty
  refine ⟨Z x,fun y hy => ?_⟩
  obtain ⟨c⟩ := A.exists_avoiding_finite_path hP hx hy
  exact c.eq_of_chart_derivative_zero hZ

/-- Actual coordinate maps on a connected complex curve minus finitely many
points differ by one global vertical rotation and translation when their
Weierstrass data differ by a unit Gauss multiplier. -/
theorem chart_weierstrass_primitives_unit_multiplier [PreconnectedSpace M] [Nonempty M]
    (A : HolomorphicCoefficientDisks M) {P : Set M} (hP : P.Finite)
    {g : M → ℂ} {dh : M → ℂ → ℂ} {c : ℂ} (hc : ‖c‖ = 1)
    {X Y : M → Fin 3 → ℝ}
    (hX : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      HasFDerivAt (fun w : ℂ => X ((chartAt ℂ p).symm w))
        (nullRealDerivative (weierstrassTriple (g ((chartAt ℂ p).symm z)) (dh p z))) z)
    (hY : ∀ p z, z ∈ ball (chartAt ℂ p p) (A.radius p) → (chartAt ℂ p).symm z ∉ P →
      HasFDerivAt (fun w : ℂ => Y ((chartAt ℂ p).symm w))
        (nullRealDerivative (weierstrassTriple (c*g ((chartAt ℂ p).symm z)) (dh p z))) z) :
    ∃ b : Fin 3 → ℝ, ∀ x ∉ P, Y x = verticalRotation c (X x)+b := by
  obtain ⟨b,hb⟩ := A.constant_of_chart_derivative_zero hP
    (Z := fun x => Y x-verticalRotation c (X x)) (by
      intro p z hz hu
      have hd := (hY p z hz hu).sub
        ((verticalRotation c).hasFDerivAt.comp z (hX p z hz hu))
      simpa only [nullRealDerivative_unit_multiplier hc,sub_self,Function.comp_def] using! hd)
  exact ⟨b,fun x hx => sub_eq_iff_eq_add.mp (hb x hx) |>.trans (add_comm _ _)⟩

end HolomorphicCoefficientDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.chart_weierstrass_primitives_unit_multiplier
