import TwoAxisHelicoid.RhombicSlopingCuts
import TwoAxisHelicoid.ExplicitMarkedReflections

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- Joint injectivity on the four boundary curves reduces the collision
test on the entire punctured torus to one point in a fixed open triangle
and one point in the bounded fundamental square. -/
theorem sloping_triangle_embedding_test {t a c : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (d : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z) :
    let L := rhombicPeriodPair t ht
    let Y := fun p : PuncturedPeriodTorus L => periodTorusLift L X per p.1
    let A := rhombicMarkedAxes t ht ∪ rhombicSlopingCycle ht false ∪ rhombicSlopingCycle ht true
    let Z := rhombicSlopingPoint t
    InjOn Y A → (Function.Injective Y ↔
      ∀ x y : ℝ, 0<y → y<x → x+y<1 → ∀ u∈Ico (0:ℝ) 1, ∀ v∈Ico (0:ℝ) 1,
        Z u v∉L.lattice → X (Z x y)=X (Z u v) → u=x ∧ v=y) := by
  intro L Y A Z graph
  let π := periodTorusProjection L
  let q := fun z (hz : z∉L.lattice) => (⟨π z,fun h => hz ((periodTorusProjection_eq_zero L z).mp h)⟩ : PuncturedPeriodTorus L)
  have triangle {x y : ℝ} (py : 0<y) (xy : y<x) (b : x+y<1) : Z x y∉L.lattice := by
    apply rhombic_open_rectangle_not_mem ht
    change (Z x y).re∈Ioo (-2:ℝ) 0 ∧ (Z x y).im∈Ioo (-t) t
    rw [(rhombicSlopingPoint_parts t x y).1,(rhombicSlopingPoint_parts t x y).2]
    exact ⟨⟨by linarith,by linarith⟩,⟨by nlinarith [mul_pos (show 0<1+y-x by linarith) ht],
      by nlinarith [mul_neg_of_neg_of_pos (sub_neg.mpr xy) ht]⟩⟩
  constructor
  · intro inj x y py xy b u hu v hv off equal
    have eq : q (Z u v) off=q (Z x y) (triangle py xy b) := inj (show Y _=Y _ from equal.symm)
    exact rhombic_sloping_square_injective ht hu hv ⟨by linarith,by linarith⟩ ⟨py.le,by linarith⟩ (congrArg Subtype.val eq)
  · intro test
    let Safe := fun z : ℂ => ∀ w∉L.lattice, X z=X w → w-z∈L.lattice
    have good {x y : ℝ} (py : 0<y) (xy : y<x) (b : x+y<1) : Safe (Z x y) := by
      intro w hw eq
      obtain ⟨u,hu,v,hv,lat⟩ := rhombic_sloping_square_rep ht w
      have hp : π (Z u v)=π w := (periodTorusProjection_eq_iff L _ _).mpr lat
      have off : Z u v∉L.lattice := fun h => hw ((periodTorusProjection_eq_zero L _).mp
        (hp.symm.trans ((periodTorusProjection_eq_zero L _).mpr h)))
      have vals : X (Z u v)=X w := congrArg (periodTorusLift L X per) hp
      obtain ⟨rfl,rfl⟩ := test x y py xy b u hu v hv off (eq.trans vals.symm)
      exact lat
    have offc {z : ℂ} (hz : z∉L.lattice) : conj z∉L.lattice := fun h =>
      hz (by simpa only [Complex.conj_conj] using rhombic_conj_mem ht h)
    have neg {z : ℂ} (hz : z∉L.lattice) (h : Safe (-z)) : Safe z := by
      intro w hw eq
      have nz := (explicit_centered_primitive_reflections ht d per z hz).1
      have nw := (explicit_centered_primitive_reflections ht d per w hw).1
      dsimp only at nz nw
      have e : X (-z)=X (-w) := sub_left_inj.mp (nz.trans (by rw [eq]; exact nw.symm))
      have lat := h (-w) (by simpa using hw) e
      have flip : -(-w- -z)=w-z := by abel
      simpa only [flip] using L.lattice.neg_mem lat
    have refl {z : ℂ} (hz : z∉L.lattice) (h : Safe (conj z)) : Safe z := by
      intro w hw eq
      have cz := (explicit_centered_primitive_reflections ht d per z hz).2
      have cw := (explicit_centered_primitive_reflections ht d per w hw).2
      dsimp only at cz cw
      have e : X (conj z)=X (conj w) := sub_left_inj.mp (cz.trans (by rw [eq]; exact cw.symm))
      simpa only [map_sub,Complex.conj_conj] using rhombic_conj_mem ht (h (conj w) (offc hw) e)
    have outside (p : PuncturedPeriodTorus L) (hp : p∉A) (v : PuncturedPeriodTorus L) (eq : Y p=Y v) : p=v := by
      obtain ⟨z,x,y,proj,py,xy,b,which⟩ := rhombic_axis_cycle_complement_triangle ht p hp
      obtain ⟨w,pw⟩ := Quotient.exists_rep v.1
      change π w=v.1 at pw
      have hz := fun h => p.2 (proj.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
      have hw := fun h => v.2 (pw.symm.trans ((periodTorusProjection_eq_zero L w).mpr h))
      have g := good py xy b
      have safe : Safe z := by
        rcases which with e|e|e|e <;> change Z x y=_ at e <;> rw [e] at g
        · exact g
        · exact refl hz g
        · exact neg hz g
        · exact refl hz (neg (offc hz) g)
      have val : X z=X w := by
        change periodTorusLift L X per p.1=periodTorusLift L X per v.1 at eq
        rwa [← proj,← pw] at eq
      exact Subtype.ext (proj.symm.trans (((periodTorusProjection_eq_iff L _ _).mpr (safe w hw val)).trans pw))
    intro p v eq
    by_cases hp : p∈A
    · by_cases hv : v∈A
      · exact graph hp hv eq
      · exact (outside v hv p eq.symm).symm
    · exact outside p hp v eq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.sloping_triangle_embedding_test
