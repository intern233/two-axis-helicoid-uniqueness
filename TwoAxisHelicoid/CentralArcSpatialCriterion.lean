import TwoAxisHelicoid.CentralFiberProjectedArcs
import TwoAxisHelicoid.ExplicitEmbeddedAxes
import TwoAxisHelicoid.ExplicitMarkedReflections

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

private theorem real_axis_representative {t : ℝ} (ht : 0<t) {x : ℝ}
    (off : (x:ℂ)∉(rhombicPeriodPair t ht).lattice) :
    ∃ u∈Ioo (0:ℝ) 2, (x:ℂ)-(u:ℂ)∈(rhombicPeriodPair t ht).lattice := by
  let k : ℤ := ⌊x/2⌋
  let u : ℝ := x-2*k
  have member : (x:ℂ)-(u:ℂ)∈(rhombicPeriodPair t ht).lattice := by
    apply (rhombic_mem_lattice_iff ht _).mpr
    refine ⟨k,0,?_,?_⟩ <;> simp [u]
  have lo : 0≤u := by dsimp [u,k]; linarith [Int.floor_le (x/2)]
  have hi : u<2 := by dsimp [u,k]; linarith [Int.lt_floor_add_one (x/2)]
  exact ⟨u,⟨lt_of_le_of_ne lo (fun h => off (by simpa [← h] using member)),hi⟩,member⟩

/-- On the central plane of a closed TwoAxisHelicoid immersion, once the positive
half period lies above the horizontal axis in the transverse coordinate,
injectivity is equivalent to just two tests on one open saddle arc.
They are positivity of its transverse displacement and simplicity of its
spatial image. Axis contacts and crossings of opposite arcs are covered. -/
theorem actual_central_spatial_embedding_test {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z)
    (mark : X 1 1<X ((1+I*t)/2) 1) :
    let L := rhombicPeriodPair t ht
    let Y := fun p : PuncturedPeriodTorus L => periodTorusLift L X per p.1
    ∃ r : ℝ → ℝ, (∀ y∈Ioo 0 t, r y∈Ioo (0:ℝ) 1) ∧ ContinuousOn r (Ioo 0 t) ∧
      (∀ y∈Ioo 0 t, r (t-y)=1-r y) ∧ r (t/2)=1/2 ∧
      let Z := fun y : ℝ => (r y:ℂ)+I*y
      (∀ y∈Ioo 0 t, X (Z y) 2=X 1 2) ∧
        (InjOn Y {p | Y p 2=X 1 2} ↔ InjOn (X ∘ Z) (Ioo 0 t) ∧ ∀ y∈Ioo 0 t, X 1 1<X (Z y) 1) := by
  intro L Y
  obtain ⟨r,inside,cont,_,_,sym,half,fiber⟩ := actual_torus_central_height_fiber ht ha d per
  refine ⟨r,inside,cont,sym,half,?_⟩
  intro Z
  let M := fun y => -conj (Z y)
  let J := Ioo (0:ℝ) t
  let R := Complex.ofReal '' Ioo (0:ℝ) 2
  let U := R ∪ Z '' J ∪ M '' J
  let π := periodTorusProjection L
  let mk := fun (z : ℂ) (hz : z∉L.lattice) =>
    (⟨π z,fun e => hz ((periodTorusProjection_eq_zero L z).mp e)⟩ : PuncturedPeriodTorus L)
  have reg {y : ℝ} (hy : y∈J) : Z y∉L.lattice := rhombic_horizontal_strip_not_mem ht
    (by change (Z y).im∈Ioo 0 t; simpa [Z,J] using hy)
  have mon (y : ℝ) : M y= -(r y:ℂ)+I*y := by apply Complex.ext <;> simp [M,Z]
  have on {y : ℝ} (hy : y∈J) : X (Z y) 2=X 1 2 :=
    (fiber _ (reg hy)).mpr (Or.inr ⟨y,hy,Or.inl (by simp [Z])⟩)
  have symm {y : ℝ} (hy : y∈J) :
      X (M y)-X 1= ![-(X (Z y)-X 1) 0,-(X (Z y)-X 1) 1,(X (Z y)-X 1) 2] := by
    have h := (explicit_centered_primitive_reflections ht d per (Z y) (reg hy)).2
    have k := (explicit_centered_primitive_reflections ht d per (conj (Z y))
      (fun mem => reg hy (by simpa using rhombic_conj_mem ht mem))).1
    change X (M y)-X 1= ![-(X (conj (Z y))-X 1) 0,(X (conj (Z y))-X 1) 1,-(X (conj (Z y))-X 1) 2] at k
    change X (conj (Z y))-X 1= ![(X (Z y)-X 1) 0,-(X (Z y)-X 1) 1,-(X (Z y)-X 1) 2] at h
    rw [h] at k
    simpa using k
  have rep (p : PuncturedPeriodTorus L) (hp : Y p 2=X 1 2) : ∃ z∈U, π z=p.1 := by
    obtain ⟨z,eq⟩ := Quotient.exists_rep p.1
    change π z=p.1 at eq
    have off : z∉L.lattice := fun h => p.2 (eq.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
    have h : X z 2=X 1 2 := by
      change periodTorusLift L X per p.1 2=_ at hp
      rwa [← eq] at hp
    rcases (fiber z off).mp h with ⟨x,k⟩|⟨y,hy,k|k⟩
    · have xr : (x:ℂ)∉L.lattice := fun h => off (by simpa using L.lattice.add_mem k h)
      obtain ⟨u,hu,ex⟩ := real_axis_representative ht xr
      have m : z-(u:ℂ)∈L.lattice := by simpa using L.lattice.add_mem k ex
      exact ⟨_,Or.inl (Or.inl ⟨u,hu,rfl⟩),((periodTorusProjection_eq_iff L _ _).mpr m).trans eq⟩
    · exact ⟨_,Or.inl (Or.inr ⟨y,hy,rfl⟩),((periodTorusProjection_eq_iff L _ _).mpr k).trans eq⟩
    · refine ⟨M y,Or.inr ⟨y,hy,rfl⟩,((periodTorusProjection_eq_iff L _ _).mpr ?_).trans eq⟩
      rwa [mon]
  refine ⟨fun y hy => on hy,?_,?_⟩
  · intro inj
    have piInj (x u : ℝ) (hx : x∈J) (hu : u∈J) (e : X (Z x)=X (Z u)) : π (Z x)=π (Z u) :=
      congrArg Subtype.val (inj (x₁:=mk (Z x) (reg hx)) (x₂:=mk (Z u) (reg hu)) (on hx) (on hu) e)
    have nozero (y : ℝ) (hy : y∈J) : X (Z y) 1≠X 1 1 := by
      intro equal
      obtain ⟨x,hx,eq⟩ := (actual_axes_coordinates_bijective ht ha one_ne_zero d).1.surjOn
        (show X (Z y) 0∈(univ:Set ℝ) from mem_univ _)
      have line := actual_primitive_horizontal_line ht d hx
      have same : X (Z y)=X (x:ℂ) := by
        funext j
        fin_cases j
        · exact eq.symm
        · exact equal.trans line.1.symm
        · exact (on hy).trans line.2.symm
      have xr := real_not_mem_rhombic_lattice_of_pos ht hx.1 hx.2
      have cong : π (x:ℂ)=π (Z y) := congrArg Subtype.val
        (inj (x₁:=mk x xr) (x₂:=mk (Z y) (reg hy)) line.2 (on hy) same.symm)
      have m := (periodTorusProjection_eq_iff L _ _).mp cong
      exact (rhombic_horizontal_strip_not_mem ht (z:=Z y-(x:ℂ)) (by change (Z y-(x:ℂ)).im∈Ioo 0 t; simpa [Z,J] using hy)) m
    have c : ContinuousOn (fun y => X (Z y) 1) J := by
      intro y hy
      have cz : ContinuousWithinAt Z J y := (continuous_ofReal.continuousAt.comp_continuousWithinAt
        (cont y hy)).add (continuous_const.mul continuous_ofReal).continuousAt.continuousWithinAt
      exact (continuous_apply 1).continuousAt.comp_continuousWithinAt ((d _ (reg hy)).continuousAt.comp_continuousWithinAt cz)
    have mid : t/2∈J := by constructor <;> linarith
    have zm : Z (t/2)=(1+I*t)/2 := by dsimp [Z]; rw [half]; push_cast; ring
    refine ⟨fun x hx u hu eq => ?_,fun y hy => ?_⟩
    · have pos (v : ℝ) (hv : v∈J) : (Z v).re∈Ioo (-1:ℝ) 1 := by
        simpa [Z] using (show r v∈Ioo (-1:ℝ) 1 from ⟨by linarith [(inside v hv).1],(inside v hv).2⟩)
      have same := rhombic_centered_open_rectangle_inj ht (pos x hx) (by simpa [Z,J] using hx)
        (pos u hu) (by simpa [Z,J] using hu) ((periodTorusProjection_eq_iff L _ _).mp (piInj x u hx hu eq).symm)
      simpa [Z] using congrArg im same
    · by_contra! h
      obtain ⟨u,hu,e⟩ := isPreconnected_Ioo.intermediate_value hy mid c
        (show X 1 1∈Icc (X (Z y) 1) (X (Z (t/2)) 1) from ⟨h,zm ▸ mark.le⟩)
      exact nozero u hu e
  · rintro ⟨arc,above⟩
    have below (y : ℝ) (hy : y∈J) : X (M y) 1<X 1 1 := by
      have e := congrFun (symm hy) 1
      change X (M y) 1-X 1 1= -(X (Z y) 1-X 1 1) at e
      linarith [above y hy]
    have lines (x : ℂ) (hx : x∈R) : X x 1=X 1 1 := by
      obtain ⟨y,hy,rfl⟩ := hx
      exact (actual_primitive_horizontal_line ht d hy).1
    have classes : InjOn X U := by
      rintro x ((hx|⟨s,hs,rfl⟩)|⟨s,hs,rfl⟩) y ((hy|⟨v,hv,rfl⟩)|⟨v,hv,rfl⟩) e
      · exact actual_primitive_injective_on_both_axes ht ha one_ne_zero d (Or.inl hx) (Or.inl hy) e
      · exact ((above v hv).ne' ((congrFun e 1).symm.trans (lines _ hx))).elim
      · exact ((below v hv).ne ((congrFun e 1).symm.trans (lines _ hx))).elim
      · exact ((above s hs).ne' ((congrFun e 1).trans (lines _ hy))).elim
      · exact congrArg Z (arc hs hv e)
      · exact ((below v hv).trans (above s hs)).ne (congrFun e.symm 1) |>.elim
      · exact ((below s hs).ne ((congrFun e 1).trans (lines _ hy))).elim
      · exact ((below s hs).trans (above v hv)).ne (congrFun e 1) |>.elim
      · have symEq := (symm hs).symm.trans ((congrArg (fun x => x-X 1) e).trans (symm hv))
        have origin : X (Z s)=X (Z v) := by
          funext j
          fin_cases j <;> [have h := congrFun symEq 0; have h := congrFun symEq 1; have h := congrFun symEq 2] <;>
            simpa using h
        exact congrArg M (arc hs hv origin)
    intro p hp q hq eq
    obtain ⟨z,hz,e⟩ := rep p hp
    obtain ⟨w,hw,f⟩ := rep q hq
    change periodTorusLift L X per p.1=periodTorusLift L X per q.1 at eq
    rw [← e,← f] at eq
    exact Subtype.ext (e.symm.trans ((congrArg π (classes hz hw eq)).trans f))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_central_spatial_embedding_test
