import TwoAxisHelicoid.PeriodicCoefficientComplexPrimitive
import TwoAxisHelicoid.TorusHeightFluxMonodromy

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology ComplexConjugate

/-- A primitive of a periodic holomorphic coefficient transforms by a
single additive complex character. This holds on the entire complement
of the lattice and allows isolated essential singularities. -/
theorem complex_primitive_lattice_character {t : ℝ} (ht : 0<t) {f F : ℂ → ℂ}
    (d : ∀ z∉(rhombicPeriodPair t ht).lattice, HasDerivAt F (f z) z)
    (periodic : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → f (z+ω)=f z) :
    let L := rhombicPeriodPair t ht
    ∃ χ : L.lattice →+ ℂ, ∀ z∉L.lattice, ∀ w : L.lattice, F (z+w)-F z=χ w := by
  let L := rhombicPeriodPair t ht
  have one : (1:ℂ)∉L.lattice := by
    simpa using real_not_mem_rhombic_lattice_of_pos ht (by norm_num : (0:ℝ)<1) (by norm_num)
  have reg {z : ℂ} (hz : z∉L.lattice) (w : L.lattice) : z+(w:ℂ)∉L.lattice :=
    fun h => hz (by simpa using L.lattice.sub_mem h w.2)
  let k := fun w : L.lattice => F (1+w)-F 1
  have equiv (z : ℂ) (hz : z∉L.lattice) (w : L.lattice) : F (z+w)-F z=k w := by
    let H := fun x : ℂ => F (x+w)-F x
    have zero (x : ℂ) (hx : x∉L.lattice) : HasDerivAt H 0 x := by
      have ds := ((d _ (reg hx w)).comp x ((hasDerivAt_id x).add_const (w:ℂ))).sub (d x hx)
      simpa only [periodic x w w.2,mul_one,sub_self] using! ds
    exact L.isClosed_lattice.isOpen_compl.is_const_of_deriv_eq_zero (rhombic_punctured_plane_isConnected ht).2
      (fun x hx => (zero x hx).differentiableAt.differentiableWithinAt) (fun x hx => (zero x hx).deriv) hz one
  let χ : L.lattice →+ ℂ := {
    toFun := k
    map_zero' := by simp [k]
    map_add' := by
      intro u v
      have e := equiv (1+(u:ℂ)) (reg one u) v
      change F (1+((u:ℂ)+v))-F 1 = (F (1+u)-F 1)+k v
      rw [← e,← add_assoc]
      abel }
  exact ⟨χ,equiv⟩

private theorem complex_period_generator_value {t : ℝ} (ht : 0<t) {f F : ℂ → ℂ}
    (an : ∀ z∉(rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (d : ∀ z∉(rhombicPeriodPair t ht).lattice, HasDerivAt F (f z) z)
    {γ : ℝ → ℂ} {v : ℂ} (dg : ∀ s : ℝ, HasDerivAt γ v s)
    (reg : ∀ s∈Icc (-1:ℝ) 1, γ s∉(rhombicPeriodPair t ht).lattice) :
    v*(∫ s : ℝ in (-1)..1, f (γ s))=F (γ 1)-F (γ (-1)) := by
  have ok (s : ℝ) (hs : s∈uIcc (-1:ℝ) 1) := reg s (by simpa only [uIcc_of_le (by norm_num : (-1:ℝ)≤1)] using hs)
  have cont : ContinuousOn (fun s => f (γ s)) (uIcc (-1:ℝ) 1) :=
    fun s hs => ((an _ (ok s hs)).continuousAt.comp (dg s).continuousAt).continuousWithinAt
  exact primitive_path_integral_eq_sub (fun s _ => dg s) (fun s hs => d _ (ok s hs)) cont.intervalIntegrable

/-- The complex character takes the literal sloping integrals of the
manuscript on the two primitive lattice generators. -/
theorem complex_character_generator_values {t : ℝ} (ht : 0<t) {f F : ℂ → ℂ}
    (an : ∀ z∉(rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (d : ∀ z∉(rhombicPeriodPair t ht).lattice, HasDerivAt F (f z) z)
    {χ : (rhombicPeriodPair t ht).lattice →+ ℂ}
    (mon : ∀ z∉(rhombicPeriodPair t ht).lattice, ∀ w : (rhombicPeriodPair t ht).lattice, F (z+w)-F z=χ w) :
    ∃ down up : (rhombicPeriodPair t ht).lattice, (down:ℂ)=1-I*t ∧ (up:ℂ)=1+I*t ∧
      χ down=rhombicDownPeriod t f ∧ χ up=rhombicUpPeriod t f := by
  let L := rhombicPeriodPair t ht
  let up : L.lattice := ⟨L.ω₂,L.ω₂_mem_lattice⟩
  let down : L.lattice := ⟨L.ω₁-L.ω₂,L.lattice.sub_mem L.ω₁_mem_lattice L.ω₂_mem_lattice⟩
  have ed : (down:ℂ)=1-I*t := by change (2:ℂ)-(1+I*t)=_; ring
  have eu : (up:ℂ)=1+I*t := rfl
  let g := originalPeriodPath t
  have raw (s : ℝ) (hs : s∈Icc (-1:ℝ) 1) := rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs)
  have cRaw (s : ℝ) (hs : s∈Icc (-1:ℝ) 1) := rhombic_open_rectangle_not_mem ht (conjugatePeriodPath_mem_rectangle ht hs)
  have endD : g 1 = g (-1)+down := by rw [ed]; simp [g,originalPeriodPath]; ring
  have endU : conj (g 1)=conj (g (-1))+up := by rw [eu]; simp [g,originalPeriodPath,map_ofNat]; ring
  refine ⟨down,up,ed,eu,?_,?_⟩
  · rw [← mon (g (-1)) (raw _ (by norm_num)) down,← endD]
    exact (complex_period_generator_value ht an d (originalPeriodPath_hasDerivAt t) raw).symm
  · rw [← mon (conj (g (-1))) (cRaw _ (by norm_num)) up,← endU]
    exact (complex_period_generator_value ht an d (conjugatePeriodPath_hasDerivAt t) cRaw).symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.complex_primitive_lattice_character
#print axioms TwoAxisHelicoid.complex_character_generator_values
