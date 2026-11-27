import TwoAxisHelicoid.RegularScalarLevelNull
import TwoAxisHelicoid.PlaneSectionCriticalSlopes

namespace TwoAxisHelicoid
open Set Complex MeasureTheory Filter Topology InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace

/-- For countably many smooth support heights, almost every slope
separates any two contacts with distinct horizontal positions.
The hypothesis is the derivative of the support height with respect
to the slope. It applies also to the height of a fixed marked point. -/
theorem ae_distinct_support_heights {ι : Type*} [Countable ι]
    (U : ι → Set ℂ) (a : ι → ℂ → ℝ) (p : ι → ℂ → ℂ)
    (smooth : ∀ i s, s∈U i → ContDiffAt ℝ 1 (a i) s)
    (rate : ∀ i s, s∈U i → ∀ v, fderiv ℝ (a i) s v= -⟪v,p i s⟫_ℝ) :
    ∀ᵐ s : ℂ, ∀ i j, s∈U i → s∈U j → a i s=a j s → p i s=p j s := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  let S := {s : ℂ | s∈U i ∧ s∈U j ∧ a i s=a j s ∧ p i s≠p j s}
  let f := fun s => a i s-a j s
  have null : volume S=0 := regular_scalar_zero_set_null (f:=f)
    (fun s h => (smooth i s h.1).sub (smooth j s h.2.1)) (fun _ h => sub_eq_zero.mpr h.2.2.1) (by
      intro s hs
      let v := p j s-p i s
      refine ⟨v,?_⟩
      have pos : 0<⟪v,v⟫_ℝ := real_inner_self_pos.mpr (sub_ne_zero.mpr hs.2.2.2.symm)
      change fderiv ℝ (a i-a j) s v≠0
      rw [fderiv_sub ((smooth i s hs.1).differentiableAt one_ne_zero)
        ((smooth j s hs.2.1).differentiableAt one_ne_zero),sub_apply,rate i s hs.1,rate j s hs.2.1]
      change 0<⟪v,p j s-p i s⟫_ℝ at pos
      rw [inner_sub_right] at pos
      linarith)
  filter_upwards [show ∀ᵐ s : ℂ, s∉S from ae_iff.mpr (by simpa only [not_not,ofPred_mem_eq] using null)] with s outside
  intro si sj eq
  by_contra distinct
  exact outside ⟨si,sj,eq,distinct⟩

/-- On one inverse branch of the Gauss slope, the derivative needed
in the measure-zero separation theorem follows from the contact
equation itself. -/
theorem graph_critical_support_branch {U : Set ℂ} {f : ℂ → ℝ} {p : ℂ → ℂ}
    (sm : ∀ s∈U, ContDiffAt ℝ 1 f (p s)) (sp : ∀ s∈U, ContDiffAt ℝ 1 p s)
    (critical : ∀ s∈U, gradient f (p s)=s) :
    let a := fun s => f (p s)-⟪s,p s⟫_ℝ
    (∀ s∈U, ContDiffAt ℝ 1 a s) ∧
    (∀ s∈U, ∀ v, fderiv ℝ a s v= -⟪v,p s⟫_ℝ) := by
  refine ⟨fun s hs => ((sm s hs).comp s (sp s hs)).sub (contDiffAt_id.inner ℝ (sp s hs)),?_⟩
  intro s hs v
  exact critical_graph_height_derivative ((sm s hs).differentiableAt one_ne_zero)
    ((sp s hs).differentiableAt one_ne_zero) (critical s hs) v

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ae_distinct_support_heights
#print axioms TwoAxisHelicoid.graph_critical_support_branch
