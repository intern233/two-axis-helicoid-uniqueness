import TwoAxisHelicoid.CentralTorusHeightFiber

namespace TwoAxisHelicoid
open Complex Set

/-- In the punctured torus the two open central arcs are disjoint, each
arc has no repeated parameter, and neither meets the open horizontal
axis. This uses the actual quotient, before applying the spatial map. -/
theorem central_height_projected_arcs_disjoint {t : ℝ} (ht : 0<t) {r : ℝ → ℝ}
    (inside : ∀ y∈Ioo 0 t, r y∈Ioo (0:ℝ) 1) :
    let L := rhombicPeriodPair t ht
    let arc := fun (positive : Bool) (y : ℝ) =>
      periodTorusProjection L ((if positive then (r y:ℂ) else -(r y:ℂ))+I*y)
    (∀ b, InjOn (arc b) (Ioo 0 t)) ∧ Disjoint (arc true '' Ioo 0 t) (arc false '' Ioo 0 t) ∧
      ∀ b, Disjoint (arc b '' Ioo 0 t) (range fun x : ℝ => periodTorusProjection L x) := by
  intro L arc
  let lift := fun (b : Bool) (y : ℝ) => (if b then (r y:ℂ) else -(r y:ℂ))+I*y
  have iy (b : Bool) (y : ℝ) : (lift b y).im=y := by cases b <;> simp [lift]
  have bx (b : Bool) {y : ℝ} (h : y∈Ioo 0 t) : (lift b y).re∈Ioo (-1:ℝ) 1 := by
    have ry := inside y h
    cases b <;> simp [lift] <;> constructor <;> linarith [ry.1,ry.2]
  have same {b c : Bool} {y v : ℝ} (hy : y∈Ioo 0 t) (hv : v∈Ioo 0 t) (eq : arc b y=arc c v) :
      lift b y=lift c v :=
    rhombic_centered_open_rectangle_inj ht (bx b hy) (by simpa [iy] using hy)
      (bx c hv) (by simpa [iy] using hv) ((periodTorusProjection_eq_iff L _ _).mp eq.symm)
  constructor
  · intro b y hy v hv eq
    simpa [iy] using congrArg im (same hy hv eq)
  constructor
  · apply disjoint_left.mpr
    rintro _ ⟨y,hy,rfl⟩ ⟨v,hv,eq⟩
    have e := congrArg re (same hv hy eq)
    simp [lift] at e
    linarith [(inside v hv).1,(inside y hy).1]
  · intro b
    apply disjoint_left.mpr
    rintro _ ⟨y,hy,rfl⟩ ⟨x,eq⟩
    have p := (periodTorusProjection_eq_iff L _ _).mp eq
    have off : lift b y-(x:ℂ)∉L.lattice := rhombic_horizontal_strip_not_mem ht
      (by change (lift b y-(x:ℂ)).im∈Ioo 0 t; simpa [iy] using hy)
    exact off p

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_height_projected_arcs_disjoint
