import TwoAxisHelicoid.CentralHeightArc
import TwoAxisHelicoid.HeightEndAxisCenter
import TwoAxisHelicoid.RhombicCenteredRectangle

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology ComplexConjugate

/-- The complete preimage of the central physical plane in the punctured
torus is the horizontal real line and the two reflected arcs joining the
saddle parameters. Congruences are modulo the actual period lattice. -/
theorem actual_torus_central_height_fiber {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z) :
    ∃ r : ℝ → ℝ, (∀ y∈Ioo 0 t, r y∈Ioo (0:ℝ) 1) ∧ ContinuousOn r (Ioo 0 t) ∧
      Tendsto r (𝓝[>] 0) (𝓝 a) ∧ Tendsto r (𝓝[<] t) (𝓝 (1-a)) ∧
      (∀ y∈Ioo 0 t, r (t-y)=1-r y) ∧ r (t/2)=1/2 ∧
      ∀ z∉(rhombicPeriodPair t ht).lattice, X z 2=X 1 2 ↔
        (∃ x : ℝ, z-(x:ℂ)∈(rhombicPeriodPair t ht).lattice) ∨
        ∃ y∈Ioo 0 t, z-((r y:ℂ)+I*y)∈(rhombicPeriodPair t ht).lattice ∨
                    z-(-(r y:ℂ)+I*y)∈(rhombicPeriodPair t ht).lattice := by
  obtain ⟨r,spec,cont,lo,hi,sym,half⟩ := actual_central_height_arc ht ha d per
  let L := rhombicPeriodPair t ht
  have height {z w : ℂ} (p : z-w∈L.lattice) : X z 2=X w 2 := by
    have e := congrFun (per w (z-w) p) 2
    rwa [show w+(z-w)=z by abel] at e
  have reflected (x y : ℝ) (hy : y∈Ioo 0 t) :
      X (-(x:ℂ)+I*y) 2=X ((x:ℂ)+I*y) 2 := by
    have off (u : ℝ) : (u:ℂ)+I*y∉L.lattice :=
      rhombic_horizontal_strip_not_mem ht (by change _∈Ioo 0 t; simpa using hy)
    have h := congrArg Complex.re (actualComplexHeight_reflection (a:=a) (c:=1) ht ((x:ℂ)+I*y))
    have conjEq : -conj ((x:ℂ)+I*y)=((-x:ℝ):ℂ)+I*y := by
      apply Complex.ext <;> simp
    rw [conjEq,Complex.conj_re,← actual_complex_height_centered_primitive ht d (off (-x)),
      ← actual_complex_height_centered_primitive ht d (off x)] at h
    simp only [ofReal_neg] at h
    linarith
  have onArc (y : ℝ) (hy : y∈Ioo 0 t) : X ((r y:ℂ)+I*y) 2=X 1 2 :=
    ((spec y hy).2 _ (spec y hy).1).mpr rfl
  have unique {x y : ℝ} (hy : y∈Ioo 0 t) (hx : x∈Icc (0:ℝ) 1)
      (eq : X ((x:ℂ)+I*y) 2=X 1 2) : x=r y :=
    (actual_quarter_height_row_strictMono ht hy d).injOn hx (Ioo_subset_Icc_self (spec y hy).1)
      (eq.trans (onArc y hy).symm)
  refine ⟨r,fun y hy => (spec y hy).1,cont,lo,hi,sym,half,?_⟩
  intro z off
  constructor
  · intro h
    obtain ⟨x,y,hx,hy,p⟩ := rhombic_centered_rectangle_rep ht z
    rcases hy.1.eq_or_lt with zero | pos
    · exact Or.inl ⟨x,by simpa [← zero] using p⟩
    · have inside : y∈Ioo 0 t := ⟨pos,hy.2⟩
      have eq := (height p).symm.trans h
      right
      refine ⟨y,inside,?_⟩
      by_cases sign : 0≤x
      · left
        rwa [← unique inside ⟨sign,hx.2.le⟩ eq]
      · right
        have eq' : X (((-x:ℝ):ℂ)+I*y) 2=X 1 2 := by simpa using (reflected x y inside).trans eq
        have e := unique inside ⟨by linarith,by linarith [hx.1]⟩ eq'
        rw [← e]
        simpa using p
  · rintro (⟨x,p⟩|⟨y,hy,p|p⟩)
    · have reg : (x:ℂ)∉L.lattice := by
        intro m
        exact off (by simpa only [sub_add_cancel] using L.lattice.add_mem p m)
      exact (height p).trans (sub_eq_zero.mp ((actual_complex_height_centered_primitive ht d reg).trans
        (actualComplexHeight_ofReal_re ht x)))
    · exact (height p).trans (onArc y hy)
    · exact (height p).trans ((reflected (r y) y hy).trans (onArc y hy))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_centered_rectangle_rep
#print axioms TwoAxisHelicoid.actual_torus_central_height_fiber
