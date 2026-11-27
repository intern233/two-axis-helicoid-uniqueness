import TwoAxisHelicoid.CentralHeightArc
import TwoAxisHelicoid.UnivalentQuarterHeightCoordinate
import TwoAxisHelicoid.HeightEndAxisCenter
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- A continuous horizontal level of a holomorphic coordinate, written
as a graph over the original imaginary coordinate, has the implicit
slope Im H′ / Re H′. Only a germ of the level identity is used. -/
theorem height_row_graph_hasDerivAt {r : ℝ → ℝ} {H : ℂ → ℂ} {c y : ℝ} {h : ℂ}
    (cr : ContinuousAt r y) (hd : HasDerivAt H h ((r y:ℂ)+I*y)) (hn : h.re≠0)
    (level : ∀ᶠ x in 𝓝 y, (H ((r x:ℂ)+I*x)).re=c) :
    HasDerivAt r (h.im/h.re) y ∧
    HasDerivAt (fun x : ℝ => (H ((r x:ℂ)+I*x)).im) (normSq h/h.re) y := by
  let z := fun x : ℝ => (r x:ℂ)+I*x
  let p₁ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let p₂ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let A : (ℝ × ℝ) →L[ℝ] ℂ := ofRealCLM.comp (h.re⁻¹ • (p₁+h.im • p₂)) + p₂.smulRight I
  let P := fun x : ℂ => ((H x).re,x.im)
  have dP := (reCLM.hasFDerivAt.comp (z y) (hd.hasFDerivAt.restrictScalars ℝ)).prodMk imCLM.hasFDerivAt
  have cz : ContinuousAt z y := (continuous_ofReal.continuousAt.comp cr).add (continuous_const.mul continuous_ofReal).continuousAt
  have line : HasDerivAt (fun x : ℝ => (c,x)) (0,1) y := (hasDerivAt_const y c).prodMk (hasDerivAt_id y)
  have eq : P ∘ z =ᶠ[𝓝 y] fun x : ℝ => (c,x) := by
    filter_upwards [level] with x hx
    exact Prod.ext hx (by simp [P,z])
  have deriv := dP.of_comp_of_leftInverse cz line.hasFDerivAt eq (f'symm:=A) (by
    intro v
    change (((h.re⁻¹*((v*h).re+h.im*v.im):ℝ):ℂ)+v.im • I)=v
    apply Complex.ext
    · simp [Complex.real_smul,Complex.mul_re]
      field_simp [hn]
      ring
    · simp [Complex.real_smul])
  have dz : HasDerivAt z (((h.im/h.re:ℝ):ℂ)+I) y := by
    have out := deriv.hasDerivAt
    change HasDerivAt z (A ((1:ℝ) • ((0,1):ℝ × ℝ))) y at out
    rw [one_smul] at out
    change HasDerivAt z (((h.re⁻¹*(0+h.im*1):ℝ):ℂ)+(1:ℝ) • I) y at out
    simpa [div_eq_inv_mul] using out
  have dx := reCLM.hasFDerivAt.comp_hasDerivAt y dz
  have dv := imCLM.hasFDerivAt.comp_hasDerivAt y (hd.scomp y dz)
  refine ⟨by simpa [z,Function.comp_def] using dx,?_⟩
  convert dv using 1
  · rfl
  · change normSq h/h.re=((((h.im/h.re:ℝ):ℂ)+I)*h).im
    simp [Complex.mul_im,Complex.normSq_apply]
    field_simp [hn]
    ring

/-- The central saddle arc is differentiable throughout its open
parameter interval. The derivative of conjugate height in that
parameter is strictly positive and has the explicit metric factor. -/
theorem actual_central_arc_derivative {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z) :
    let H := actualComplexHeight t a 1 ht
    ∃ r : ℝ → ℝ, ∀ y∈Ioo 0 t, r y∈Ioo (0:ℝ) 1 ∧ X ((r y:ℂ)+I*y) 2=X 1 2 ∧
      let h := coordinateData t a 1 ht ((r y:ℂ)+I*y) 2
      HasDerivAt r (h.im/h.re) y ∧
        HasDerivAt (fun x : ℝ => (H ((r x:ℂ)+I*x)).im) (normSq h/h.re) y ∧ 0<normSq h/h.re := by
  intro H
  obtain ⟨r,spec,cr,_⟩ := actual_central_height_arc ht ha d per
  let z := fun y : ℝ => (r y:ℂ)+I*y
  have eq (y : ℝ) (hy : y∈Ioo 0 t) := ((spec y hy).2 _ (spec y hy).1).mpr rfl
  have inside (y : ℝ) (hy : y∈Ioo 0 t) : z y∈complexOpenRect 0 1 0 t :=
    ⟨by simpa [z] using (spec y hy).1,by simpa [z] using hy⟩
  refine ⟨r,?_⟩
  intro y hy
  let h := coordinateData t a 1 ht (z y) 2
  have dh : HasDerivAt H h (z y) := actualComplexHeight_hasDerivAt ht (rhombic_horizontal_strip_not_mem ht (inside y hy).2)
  have pos : 0<h.re := dh.deriv ▸ (actual_complex_height_univalent_quarter (a:=a) ht).1 (z y) (inside y hy)
  have result := height_row_graph_hasDerivAt ((cr y hy).continuousAt (isOpen_Ioo.mem_nhds hy)) dh pos.ne' (c:=0) (by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with x hx
    have v := actual_complex_height_centered_primitive ht d (rhombic_horizontal_strip_not_mem ht (inside x hx).2)
    rw [show X (z x) 2=X 1 2 from eq x hx,sub_self] at v
    exact v.symm)
  have nonzero : h≠0 := fun hz => pos.ne' (congrArg Complex.re hz)
  exact ⟨(spec y hy).1,eq y hy,result.1,result.2,div_pos (normSq_pos.mpr nonzero) pos⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_central_arc_derivative
