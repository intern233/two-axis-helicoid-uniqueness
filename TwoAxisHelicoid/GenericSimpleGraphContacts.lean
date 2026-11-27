import TwoAxisHelicoid.CountableGraphSlopeInverses
import TwoAxisHelicoid.GenericCriticalSupportHeights

namespace TwoAxisHelicoid
open Complex Set MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace ContDiff

/-- Almost every tilted linear height has nondegenerate contacts at
distinct heights on a countable family of graph patches. If one
contact has the same height as a prescribed marked point, they are
the same point in ambient three-space. Overlaps of chart images are
allowed. -/
theorem ae_simple_graph_plane_contacts {ι : Type*} [Countable ι]
    (D : ι → Set ℂ) (f : ι → ℂ → ℝ)
    (smooth : ∀ i x, x∈D i → ContDiffAt ℝ 3 (f i) x) (mark : ℂ × ℝ) :
    ∀ᵐ s : ℂ, ∀ i x, x∈D i → gradient (f i) x=s →
      (fderiv ℝ (gradient (f i)) x).det≠0 ∧
      (∀ j y, y∈D j → gradient (f j) y=s →
        f i x-⟪s,x⟫_ℝ=f j y-⟪s,y⟫_ℝ → (x,f i x)=(y,f j y)) ∧
      (f i x-⟪s,x⟫_ℝ=mark.2-⟪s,mark.1⟫_ℝ → (x,f i x)=mark) := by
  classical
  choose C ct V P inv cover using fun i => countable_graph_slope_inverses (smooth i)
  let _ (i : ι) : Countable (C i) := (ct i).to_subtype
  let J := (Σ i, C i) ⊕ Unit
  let U : J → Set ℂ := Sum.elim (fun j => V j.1 j.2) (fun _ => univ)
  let p : J → ℂ → ℂ := Sum.elim (fun j => P j.1 j.2) (fun _ _ => mark.1)
  let a : J → ℂ → ℝ := Sum.elim
    (fun j s => f j.1 (P j.1 j.2 s)-⟪s,P j.1 j.2 s⟫_ℝ)
    (fun _ s => mark.2-⟪s,mark.1⟫_ℝ)
  have branches (j : Σ i, C i) := graph_critical_support_branch
    (fun s hs => (inv j.1 j.2 s hs).2.1) (fun s hs => (inv j.1 j.2 s hs).1)
    (fun s hs => (inv j.1 j.2 s hs).2.2)
  have smoothA (j : J) (s : ℂ) (hs : s∈U j) : ContDiffAt ℝ 1 (a j) s := by
    cases j with
    | inl j => exact (branches j).1 s hs
    | inr _ => exact contDiffAt_const.sub (contDiffAt_id.inner ℝ contDiffAt_const)
  have rate (j : J) (s : ℂ) (hs : s∈U j) (v : ℂ) : fderiv ℝ (a j) s v= -⟪v,p j s⟫_ℝ := by
    cases j with
    | inl j => exact (branches j).2 s hs v
    | inr _ =>
      have form : a (.inr ())=(fun t : ℂ => mark.2-innerSL ℝ mark.1 t) :=
        funext fun t => congrArg (fun r : ℝ => mark.2-r) (real_inner_comm _ _)
      change fderiv ℝ (a (.inr ())) s v= -⟪v,mark.1⟫_ℝ
      rw [form,((innerSL ℝ mark.1).hasFDerivAt.const_sub mark.2).fderiv]
      simp [real_inner_comm]
  filter_upwards [ae_nondegenerate_graph_height_slopes D f
    (fun i x hx => (smooth i x hx).of_le (by norm_num)),ae_distinct_support_heights U a p smoothA rate] with s good separate
  intro i x hx critical
  have det := good i x hx critical
  obtain ⟨k,hk,ek⟩ := cover i x hx det
  rw [critical] at hk ek
  refine ⟨det,?_,?_⟩
  · intro j y hy crit equal
    obtain ⟨l,hl,el⟩ := cover j y hy (good j y hy crit)
    rw [crit] at hl el
    let u : J := .inl ⟨i,k⟩
    let v : J := .inl ⟨j,l⟩
    have sep := separate u v hk hl (show a u s=a v s by simpa [a,u,v,ek,el] using equal)
    have xy : x=y := by simpa [p,u,v,ek,el] using sep
    rw [xy] at equal ⊢
    exact Prod.ext rfl (sub_left_inj.mp equal)
  · intro equal
    let u : J := .inl ⟨i,k⟩
    let v : J := .inr ()
    have sep := separate u v hk (mem_univ s) (show a u s=a v s by simpa [a,u,v,ek] using equal)
    have xy : x=mark.1 := by simpa [p,u,v,ek] using sep
    exact Prod.ext xy (sub_left_inj.mp (by simpa only [xy] using equal))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ae_simple_graph_plane_contacts
