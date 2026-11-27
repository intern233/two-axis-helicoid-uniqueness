import TwoAxisHelicoid.RealDerivativeSign
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000

theorem positive_inverse_square_derivative_left_limit {f d : ℝ → ℝ} {a r C : ℝ}
    (har : a < r) (hC : 0 < C) (hf : ∀ x ∈ Ioo a r, HasDerivAt f (d x) x)
    (hbnd : ∀ᶠ x in 𝓝[>] a, C/(x-a)^2 ≤ d x) :
    Tendsto f (𝓝[>] a) atBot := by
  obtain ⟨b₀,hb₀,hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbnd
  let b := min b₀ r
  have hab : a < b := lt_min hb₀ har
  have hsub : Ioo a b ⊆ Ioo a r := fun x hx => ⟨hx.1,hx.2.trans_le (min_le_right _ _)⟩
  have hbound' (x : ℝ) (hx : x ∈ Ioo a b) : C/(x-a)^2 ≤ d x :=
    hbound ⟨hx.1,hx.2.trans_le (min_le_left _ _)⟩
  let g : ℝ → ℝ := fun x => f x+C/(x-a)
  have hg (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt g (d x-C/(x-a)^2) x := by
    have hi := (((hasDerivAt_id x).sub_const a).inv (sub_ne_zero.mpr hx.1.ne')).const_mul C
    convert (hf x (hsub hx)).add hi using 1
    · ext u
      simp [g,div_eq_mul_inv]
    · dsimp only [id_eq]
      ring
  have hm : MonotoneOn g (Ioo a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo a b)
      (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hg x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [isOpen_Ioo.interior_eq] at hx
    rw [(hg x hx).deriv]
    exact sub_nonneg.mpr (hbound' x hx)
  obtain ⟨x₀,hx₀a,hx₀b⟩ := exists_between hab
  have hshift : Tendsto (fun x : ℝ => x-a) (𝓝[>] a) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [sub_self] using
        (show Tendsto (fun x : ℝ => x-a) (𝓝[>] a) (𝓝 (a-a)) from
          (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (show a < x from hx)
  have hblow : Tendsto (fun x : ℝ => C/(x-a)) (𝓝[>] a) atTop := by
    simpa only [div_eq_mul_inv,Function.comp_def] using (tendsto_inv_nhdsGT_zero.comp hshift).const_mul_atTop hC
  apply Filter.tendsto_atBot.mpr
  intro R
  filter_upwards [Ioo_mem_nhdsGT hx₀a,hblow.eventually_ge_atTop (g x₀-R)] with x hx hb
  have hgx := hm ⟨hx.1,hx.2.trans hx₀b⟩ ⟨hx₀a,hx₀b⟩ hx.2.le
  dsimp only [g] at hgx hb
  linarith

theorem real_neg_tendsto_nhdsGT (a : ℝ) :
    Tendsto (fun x : ℝ => -x) (𝓝[>] a) (𝓝[<] (-a)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact neg_lt_neg (show a < x from hx)

theorem real_neg_tendsto_nhdsLT (a : ℝ) :
    Tendsto (fun x : ℝ => -x) (𝓝[<] a) (𝓝[>] (-a)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact neg_lt_neg (show x < a from hx)

theorem positive_inverse_square_derivative_right_limit {f d : ℝ → ℝ} {a b C : ℝ}
    (hab : a < b) (hC : 0 < C) (hf : ∀ x ∈ Ioo a b, HasDerivAt f (d x) x)
    (hbnd : ∀ᶠ x in 𝓝[<] b, C/(b-x)^2 ≤ d x) :
    Tendsto f (𝓝[<] b) atTop := by
  have hneg : Tendsto (fun x : ℝ => -x) (𝓝[>] (-b)) (𝓝[<] b) := by
    simpa only [neg_neg] using real_neg_tendsto_nhdsGT (-b)
  have hD (x : ℝ) (hx : x ∈ Ioo (-b) (-a)) : HasDerivAt (fun x => -f (-x)) (d (-x)) x := by
    have hi : -x ∈ Ioo a b := ⟨by linarith [hx.2],by linarith [hx.1]⟩
    convert (hf (-x) hi).neg.comp x (hasDerivAt_neg x) using 1
    · rfl
    · simp
  have hB : ∀ᶠ x in 𝓝[>] (-b), C/(x-(-b))^2 ≤ d (-x) := by
    filter_upwards [hneg.eventually hbnd] with x hx
    simpa only [sub_neg_eq_add,add_comm] using hx
  have hL := positive_inverse_square_derivative_left_limit (neg_lt_neg hab) hC hD hB
  have he := hL.comp (real_neg_tendsto_nhdsLT b)
  simpa only [Function.comp_def,neg_neg] using tendsto_neg_atBot_atTop.comp he

theorem positive_inverse_square_derivative_surjective {f d : ℝ → ℝ} {a b C : ℝ}
    (hab : a < b) (hC : 0 < C) (hf : ∀ x ∈ Ioo a b, HasDerivAt f (d x) x)
    (hleft : ∀ᶠ x in 𝓝[>] a, C/(x-a)^2 ≤ d x)
    (hright : ∀ᶠ x in 𝓝[<] b, C/(b-x)^2 ≤ d x) :
    SurjOn f (Ioo a b) univ := by
  have hL := positive_inverse_square_derivative_left_limit hab hC hf hleft
  have hR := positive_inverse_square_derivative_right_limit hab hC hf hright
  exact (convex_Ioo a b).isPreconnected.intermediate_value_Iii
    (le_principal_iff.mpr (Ioo_mem_nhdsGT hab)) (le_principal_iff.mpr (Ioo_mem_nhdsLT hab))
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt) hL hR

/-- Nonvanishing velocity and inverse-square growth at both endpoints force
a real coordinate to cover the whole line. -/
theorem inverse_square_nonzero_derivative_surjective {f d : ℝ → ℝ} {a b C : ℝ}
    (hab : a < b) (hC : 0 < C) (hf : ∀ x ∈ Ioo a b, HasDerivAt f (d x) x)
    (hd : ContinuousOn d (Ioo a b)) (hn : ∀ x ∈ Ioo a b, d x ≠ 0)
    (hleft : ∀ᶠ x in 𝓝[>] a, C/(x-a)^2 ≤ |d x|)
    (hright : ∀ᶠ x in 𝓝[<] b, C/(b-x)^2 ≤ |d x|) :
    SurjOn f (Ioo a b) univ := by
  rcases continuous_nonzero_constant_sign (convex_Ioo a b).isPreconnected
      (nonempty_Ioo.mpr hab) hd hn with hp | hm
  · apply positive_inverse_square_derivative_surjective hab hC hf
    · filter_upwards [hleft,Ioo_mem_nhdsGT hab] with x hx hmem
      simpa only [abs_of_pos (hp x hmem)] using hx
    · filter_upwards [hright,Ioo_mem_nhdsLT hab] with x hx hmem
      simpa only [abs_of_pos (hp x hmem)] using hx
  · have hneg : SurjOn (fun x => -f x) (Ioo a b) univ := by
      apply positive_inverse_square_derivative_surjective hab hC (fun x hx => (hf x hx).neg)
      · filter_upwards [hleft,Ioo_mem_nhdsGT hab] with x hx hmem
        simpa only [abs_of_neg (hm x hmem)] using hx
      · filter_upwards [hright,Ioo_mem_nhdsLT hab] with x hx hmem
        simpa only [abs_of_neg (hm x hmem)] using hx
    intro y _
    obtain ⟨x,hx,he⟩ := hneg (show -y ∈ (univ : Set ℝ) from mem_univ _)
    exact ⟨x,hx,by linarith⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.inverse_square_nonzero_derivative_surjective
