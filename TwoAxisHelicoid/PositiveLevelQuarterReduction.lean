import TwoAxisHelicoid.ActualQuarterHeightSlices
import TwoAxisHelicoid.ExplicitMarkedReflections
import TwoAxisHelicoid.RhombicCenteredRectangle
import TwoAxisHelicoid.HeightEndAxisCenter

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- Two overlapping monotone arcs can be joined when the early
portion and the late portion are separated in one of the two spatial
coordinates, with a bounded transition interval in the middle. -/
theorem quarter_arc_injective_from_windows {b l u w t C : ℝ} {F : ℝ → Fin 3 → ℝ}
    (early : StrictMonoOn (fun y => F y 1) (Icc b u))
    (late : StrictAntiOn (fun y => F y 0) (Ico l t))
    (start : ∀ y∈Ico b t, y<l → 0≤F y 0 ∧ F y 1≤C)
    (middle : ∀ y∈Ico b t, u<y → y≤w → C<F y 1)
    (finish : ∀ y∈Ico b t, w<y → F y 0<0) : InjOn F (Ico b t) := by
  have separate {x y : ℝ} (hx : x∈Ico b t) (hy : y∈Ico b t) (order : x<y) : F x≠F y := by
    intro eq
    by_cases ey : y≤u
    · exact (early ⟨hx.1,order.le.trans ey⟩ ⟨hy.1,ey⟩ order).ne (congrFun eq 1)
    by_cases lx : l≤x
    · exact (late ⟨lx,hx.2⟩ ⟨lx.trans order.le,hy.2⟩ order).ne (congrFun eq.symm 0)
    obtain ⟨pos,below⟩ := start x hx (lt_of_not_ge lx)
    rcases le_or_gt y w with small|big
    · exact (below.trans_lt (middle y hy (lt_of_not_ge ey) small)).ne (congrFun eq 1)
    · exact (finish y hy big).not_ge ((congrFun eq 0) ▸ pos)
  intro x hx y hy eq
  exact lt_trichotomy x y |>.resolve_left (fun lt => separate hx hy lt eq) |>.resolve_right
    (fun lt => separate hy hx lt eq.symm)

/-- The full positive level is embedded once the first-quarter part
is injective and its open part stays on the positive transverse side.
The marked vertical axis, the horizontal real line, reflected points
and the punctures are all accounted for. -/
theorem positive_level_injective_from_quarter {t a h : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hp : 0<h)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z)
    (simple : InjOn X {z : ℂ | z.re∈Ioc (0:ℝ) 1 ∧ z.im∈Ioo (0:ℝ) t ∧ X z 2=X 1 2+h})
    (side : ∀ z : ℂ, z.re∈Ioo (0:ℝ) 1 → z.im∈Ioo (0:ℝ) t → X z 2=X 1 2+h → X 1 1<X z 1) :
    let L := rhombicPeriodPair t ht
    let Y := fun q : PuncturedPeriodTorus L => periodTorusLift L X per q.1
    InjOn Y {q | Y q 2=X 1 2+h} := by
  intro L Y
  let Z := fun x y : ℝ => (x:ℂ)+I*y
  let V := fun x y : ℝ => X (Z x y)-X 1
  have mirror (x y : ℝ) (hy : y∈Ioo 0 t) :
      V (-x) y= ![-V x y 0,-V x y 1,V x y 2] := by
    have off : Z x y∉L.lattice := rhombic_horizontal_strip_not_mem ht (by change (Z x y).im∈Ioo 0 t; simpa [Z] using hy)
    have oc : conj (Z x y)∉L.lattice := fun m => off (by simpa using rhombic_conj_mem ht m)
    have c := (explicit_centered_primitive_reflections ht d per _ off).2
    have n := (explicit_centered_primitive_reflections ht d per _ oc).1
    have flip : Z (-x) y= -conj (Z x y) := by apply Complex.ext <;> simp [Z]
    dsimp only [V]
    rw [flip]
    dsimp only at c n
    rw [n,c]
    ext j
    fin_cases j <;> simp
  have rep (q : PuncturedPeriodTorus L) (hit : Y q 2=X 1 2+h) :
      ∃ x∈Ico (-1:ℝ) 1, ∃ y∈Ioo (0:ℝ) t, x≠0 ∧ periodTorusProjection L (Z x y)=q.1 ∧ X (Z x y)=Y q := by
    obtain ⟨z,proj⟩ := Quotient.exists_rep q.1
    change periodTorusProjection L z=q.1 at proj
    obtain ⟨x,y,hx,hy,lat⟩ := rhombic_centered_rectangle_rep ht z
    have eq := ((periodTorusProjection_eq_iff L (Z x y) z).mpr lat).trans proj
    have same : X (Z x y)=Y q := congrArg (periodTorusLift L X per) eq
    have off : Z x y∉L.lattice := fun m => q.2 (eq.symm.trans ((periodTorusProjection_eq_zero L _).mpr m))
    have inside : 0<y := by
      rcases hy.1.eq_or_lt with zero|pos
      · have real : Z x y=(x:ℂ) := by simp [Z,← zero]
        have c := actual_complex_height_centered_primitive ht d off
        rw [real,actualComplexHeight_ofReal_re ht] at c
        rw [← same,real] at hit
        linarith
      · exact pos
    have yt : y∈Ioo 0 t := ⟨inside,hy.2⟩
    refine ⟨x,hx,y,yt,?_,eq,same⟩
    intro zero
    obtain ⟨u,⟨ui,level⟩,_⟩ := actual_quarter_central_plane_unique ht ha yt d per
    have cmp := actual_quarter_height_row_strictMono ht yt d (show (0:ℝ)∈Icc 0 1 by norm_num) (Ioo_subset_Icc_self ui) ui.1
    change X (Z 0 y) 2<X (Z u y) 2 at cmp
    rw [← zero,same,hit,show X (Z u y) 2=X 1 2 from level] at cmp
    linarith
  let In := fun x y : ℝ => x∈Ioc (0:ℝ) 1 ∧ y∈Ioo (0:ℝ) t ∧ V x y 2=h
  have member {x y : ℝ} (m : In x y) : Z x y∈{z : ℂ | z.re∈Ioc (0:ℝ) 1 ∧ z.im∈Ioo (0:ℝ) t ∧ X z 2=X 1 2+h} := by
    have e := m.2.2
    change X (Z x y) 2-X 1 2=h at e
    exact ⟨by simpa [Z] using m.1,by simpa [Z] using m.2.1,by linarith⟩
  have above {x y : ℝ} (m : In x y) (right : x<1) : 0<V x y 1 := by
    exact sub_pos.mpr (side _ (by simpa [Z] using And.intro m.1.1 right) (member m).2.1 (member m).2.2)
  have weak {x y : ℝ} (m : In x y) : 0≤V x y 1 := by
    rcases m.1.2.lt_or_eq with lt|one
    · exact (above m lt).le
    · subst x
      have axis := (actual_primitive_vertical_line ht d (show y∈Ioo (-t) t from ⟨by linarith [m.2.1.1],m.2.1.2⟩)).2
      simp [V,Z,axis]
  have negative {x y : ℝ} (hx : x∈Ico (-1:ℝ) 1) (nx : x<0) (hy : y∈Ioo 0 t) (lev : V x y 2=h) : In (-x) y :=
    ⟨⟨neg_pos.mpr nx,by linarith [hx.1]⟩,hy,(congrFun (mirror x y hy) 2).trans lev⟩
  intro p ph q qh same
  obtain ⟨x,hx,y,hy,nx,px,valx⟩ := rep p ph
  obtain ⟨u,hu,v,hv,nu,pu,valu⟩ := rep q qh
  have eq : V x y=V u v := congrArg (fun w => w-X 1) (valx.trans (same.trans valu.symm))
  have height {s : PuncturedPeriodTorus L} {x y : ℝ} (level : Y s 2=X 1 2+h) (e : X (Z x y)=Y s) : V x y 2=h := by
    change X (Z x y) 2-X 1 2=h
    rw [e,level]
    ring
  have xh := height ph valx
  have uh := height qh valu
  have collide {x y u v : ℝ} (a : In x y) (b : In u v) (e : V x y=V u v) : Z x y=Z u v :=
    simple (member a) (member b) (sub_left_inj.mp e)
  have cross {x y u v : ℝ} (a : In x y) (right : x<1) (b : In (-u) v) (e : V x y=V u v) : False := by
    have one := above a right
    have two := weak b
    have m := congrFun (mirror u v b.2.1) 1
    change V (-u) v 1= -(V u v 1) at m
    rw [← e] at m
    linarith
  have equal : Z x y=Z u v := by
    rcases lt_or_gt_of_ne nx with xn|xp <;> rcases lt_or_gt_of_ne nu with un|up
    · have se : V (-x) y=V (-u) v := (mirror x y hy).trans (by rw [eq]; exact (mirror u v hv).symm)
      have e := collide (negative hx xn hy xh) (negative hu un hv uh) se
      have re := congrArg Complex.re e
      have im := congrArg Complex.im e
      simp [Z] at re im
      rw [re,im]
    · exact (cross ⟨⟨up,hu.2.le⟩,hv,uh⟩ hu.2 (negative hx xn hy xh) eq.symm).elim
    · exact (cross ⟨⟨xp,hx.2.le⟩,hy,xh⟩ hx.2 (negative hu un hv uh) eq).elim
    · exact collide ⟨⟨xp,hx.2.le⟩,hy,xh⟩ ⟨⟨up,hu.2.le⟩,hv,uh⟩ eq
  exact Subtype.ext (px.symm.trans ((congrArg (periodTorusProjection L) equal).trans pu))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarter_arc_injective_from_windows
#print axioms TwoAxisHelicoid.positive_level_injective_from_quarter
