import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

private theorem real_jet_conj {f : ℂ → ℂ} (h : ∀ z, f (conj z)=conj (f z)) :
    ∀ z, deriv f (conj z)=conj (deriv f z) := by
  have id : conj ∘ f ∘ conj=f := by funext z; simp [Function.comp_def,h]
  have eq := deriv_conj_conj (f:=f)
  rw [id] at eq
  intro z
  simpa [Function.comp_def] using congrFun eq (conj z)

private theorem real_jet_im_zero {f : ℂ → ℂ} (h : ∀ z, f (conj z)=conj (f z)) (x : ℝ) : (f x).im=0 := by
  have e := congrArg im (h (x:ℂ))
  simp only [conj_ofReal,conj_im] at e
  linarith

theorem vertical_line_real_derivatives {f : ℂ → ℂ} {x y : ℝ} {v : ℂ}
    (h : HasDerivAt f v ((x:ℂ)+I*y)) :
    HasDerivAt (fun s : ℝ => (f ((x:ℂ)+I*s)).re) (-v.im) y ∧
    HasDerivAt (fun s : ℝ => (f ((x:ℂ)+I*s)).im) v.re y := by
  have line : HasDerivAt (fun s : ℝ => (x:ℂ)+I*s) I y := by
    simpa using ((hasDerivAt_id y).ofReal_comp.const_mul I).const_add (x:ℂ)
  have d := h.scomp y line
  have r := reCLM.hasFDerivAt.comp_hasDerivAt y d
  have i := imCLM.hasFDerivAt.comp_hasDerivAt y d
  change HasDerivAt _ (I*v).re y at r
  change HasDerivAt _ (I*v).im y at i
  exact ⟨I_mul_re v ▸ r,I_mul_im v ▸ i⟩

theorem horizontal_line_im_derivative {f : ℂ → ℂ} {x y : ℝ} {v : ℂ}
    (h : HasDerivAt f v ((x:ℂ)+I*y)) :
    HasDerivAt (fun s : ℝ => (f ((s:ℂ)+I*y)).im) v.im x := by
  have line : HasDerivAt (fun s : ℝ => (s:ℂ)+I*y) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp.add_const (I*(y:ℂ))
  have i := imCLM.hasFDerivAt.comp_hasDerivAt x (h.scomp x line)
  change HasDerivAt (fun s : ℝ => (f ((s:ℂ)+I*y)).im) ((1:ℂ)*v).im x at i
  rwa [one_mul] at i

/-- Two analytic derivative signs on a closed rectangle imply a strict
quadrant on its interior. The zero at the upper left corner is allowed. -/
theorem rectangle_quadrant_of_real_jets {a b h : ℝ} (ab : a<b) (hh : 0<h) {f : ℂ → ℂ}
    (realAxis : ∀ z, f (conj z)=conj (f z))
    (analytic : ∀ x∈Icc a b, ∀ y∈Icc 0 h, AnalyticAt ℂ f ((x:ℂ)+I*y))
    (bottom : ∀ x∈Icc a b, (f (x:ℂ)).re≤0)
    (top : 0≤(f ((a:ℂ)+I*h)).im)
    (second : ∀ x∈Icc a b, ∀ y∈Icc 0 h, 0<(deriv (deriv f) ((x:ℂ)+I*y)).re)
    (third : ∀ y∈Icc 0 h, 0≤(deriv (deriv (deriv f)) ((a:ℂ)+I*y)).re) :
    ∀ x∈Ioc a b, ∀ y∈Ioc 0 h, (f ((x:ℂ)+I*y)).re<0 ∧ 0<(f ((x:ℂ)+I*y)).im := by
  let Z := fun x y : ℝ => (x:ℂ)+I*y
  let J := Icc 0 h
  have lo : (0:ℝ)∈J := left_mem_Icc.mpr hh.le
  have hi : h∈J := right_mem_Icc.mpr hh.le
  have left : a∈Icc a b := left_mem_Icc.mpr ab.le
  have atZero (x : ℝ) : Z x 0=(x:ℂ) := by simp [Z]
  have df := real_jet_conj realAxis
  have ddf := real_jet_conj df
  have positive (x : ℝ) (hx : x∈Icc a b) {y : ℝ} (hy : y∈Ioc 0 h) : 0<(deriv f (Z x y)).im := by
    have slope (s : ℝ) (hs : s∈J) := (vertical_line_real_derivatives (analytic x hx s hs).deriv.differentiableAt.hasDerivAt).2
    have inc : StrictMonoOn (fun u => (deriv f (Z x u)).im) J :=
      strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun s hs => (slope s hs).continuousAt.continuousWithinAt)
        (fun s hs => (slope s (interior_subset hs)).deriv.symm ▸ second x hx s (interior_subset hs))
    simpa only [atZero,real_jet_im_zero df] using inc lo ⟨hy.1.le,hy.2⟩ hy.1
  have nonneg2 (y : ℝ) (hy : y∈J) : 0≤(deriv (deriv f) (Z a y)).im := by
    have slope (s : ℝ) (hs : s∈J) := (vertical_line_real_derivatives (analytic a left s hs).deriv.deriv.differentiableAt.hasDerivAt).2
    have inc : MonotoneOn (fun u => (deriv (deriv f) (Z a u)).im) J :=
      monotoneOn_of_deriv_nonneg (convex_Icc _ _) (fun s hs => (slope s hs).continuousAt.continuousWithinAt)
        (fun s hs => (slope s (interior_subset hs)).differentiableAt.differentiableWithinAt)
        (fun s hs => (slope s (interior_subset hs)).deriv.symm ▸ third s (interior_subset hs))
    simpa only [atZero,real_jet_im_zero ddf] using inc lo hy hy.1
  have edge : ConcaveOn ℝ J (fun y => (f (Z a y)).im) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (f':=fun y => (deriv f (Z a y)).re) (f'':=fun y => -(deriv (deriv f) (Z a y)).im)
    · exact fun s hs => (vertical_line_real_derivatives (analytic a left s hs).differentiableAt.hasDerivAt).2.continuousAt.continuousWithinAt
    · exact fun s hs => (vertical_line_real_derivatives (analytic a left s (interior_subset hs)).differentiableAt.hasDerivAt).2.hasDerivWithinAt
    · exact fun s hs => (vertical_line_real_derivatives (analytic a left s (interior_subset hs)).deriv.differentiableAt.hasDerivAt).1.hasDerivWithinAt
    · exact fun s hs => neg_nonpos.mpr (nonneg2 s (interior_subset hs))
  have start : 0≤(f (Z a 0)).im := by rw [atZero,real_jet_im_zero realAxis]
  intro x hx y hy
  have xc : x∈Icc a b := ⟨hx.1.le,hx.2⟩
  have yc : y∈J := ⟨hy.1.le,hy.2⟩
  have dec : StrictAntiOn (fun v => (f (Z x v)).re) J := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (fun s hs =>
      (vertical_line_real_derivatives (analytic x xc s hs).differentiableAt.hasDerivAt).1.continuousAt.continuousWithinAt)
    intro s hs
    change s∈interior (Icc _ _) at hs
    rw [interior_Icc] at hs
    exact (vertical_line_real_derivatives (analytic x xc s ⟨hs.1.le,hs.2.le⟩).differentiableAt.hasDerivAt).1.deriv.trans_lt
      (neg_lt_zero.mpr (positive x xc ⟨hs.1,hs.2.le⟩))
  have inc : StrictMonoOn (fun v => (f (Z v y)).im) (Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun u hu =>
      (horizontal_line_im_derivative (analytic u hu y yc).differentiableAt.hasDerivAt).continuousAt.continuousWithinAt)
      (fun u hu => (horizontal_line_im_derivative (analytic u (interior_subset hu) y yc).differentiableAt.hasDerivAt).deriv.symm ▸
        positive u (interior_subset hu) hy)
  have atLeft : 0≤(f (Z a y)).im := ((edge.convex_ge 0).ordConnected.out ⟨lo,start⟩ ⟨hi,top⟩ yc).2
  have base : (f (Z x 0)).re≤0 := by rw [atZero]; exact bottom x xc
  exact ⟨(dec lo yc hy.1).trans_le base,atLeft.trans_lt (inc left xc hx.1)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangle_quadrant_of_real_jets
