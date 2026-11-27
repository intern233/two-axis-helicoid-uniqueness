import TwoAxisHelicoid.CentralHeightArc
import TwoAxisHelicoid.ExplicitMarkedReflections
import TwoAxisHelicoid.RhombicCenteredRectangle

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology ComplexConjugate

/-- The two diagonal corners are the only punctures in the closed
first quarter. Each of the four regular edges lies in one of the two
axis lines and hence has zero centered transverse coordinate. -/
theorem quarter_rectangle_punctures_and_axes {t a : ℝ} (ht : 0<t)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z)
    {z : ℂ} (hx : z.re∈Icc (0:ℝ) 1) (hy : z.im∈Icc (0:ℝ) t) :
    (z∈(rhombicPeriodPair t ht).lattice → z=0 ∨ z=1+I*t) ∧
    (z∉(rhombicPeriodPair t ht).lattice → (z.re=0 ∨ z.re=1 ∨ z.im=0 ∨ z.im=t) → X z 1=X 1 1) := by
  let L := rhombicPeriodPair t ht
  have shift : (-1+I*(t:ℂ))∈L.lattice := (rhombic_mem_lattice_iff ht _).mpr ⟨-1,1,by norm_num,by simp⟩
  constructor
  · intro punct
    rcases hy.1.eq_or_lt with zero|pos
    · left
      have eq : z=((z.re:ℝ):ℂ) := Complex.ext rfl (by simp [← zero])
      rcases hx.1.eq_or_lt with x0|xp
      · exact Complex.ext x0.symm zero.symm
      · exact (real_not_mem_rhombic_lattice_of_pos ht xp (by linarith [hx.2]) (eq ▸ punct)).elim
    · rcases hy.2.lt_or_eq with lt|top
      · exact (rhombic_horizontal_strip_not_mem ht (show z.im∈Ioo 0 t from ⟨pos,lt⟩) punct).elim
      · right
        rcases hx.2.lt_or_eq with lt|one
        · have e : z-(-1+I*(t:ℂ))=((z.re+1:ℝ):ℂ) := by apply Complex.ext <;> simp [top]
          have mem := L.lattice.sub_mem punct shift
          rw [e] at mem
          exact (real_not_mem_rhombic_lattice_of_pos ht (by linarith [hx.1]) (by linarith) mem).elim
        · apply Complex.ext <;> simp [one,top]
  · intro off sides
    have axis {w : ℂ} (same : X w=X z)
        (reflection : X w 1-X 1 1= -(X z 1-X 1 1)) : X z 1=X 1 1 := by rw [same] at reflection; linarith
    have h := explicit_centered_primitive_reflections ht d per z off
    have reg : conj z∉L.lattice := fun k => off (by simpa using rhombic_conj_mem ht k)
    have v := congrFun (explicit_centered_primitive_reflections ht d per (conj z) reg).1 1
    have c := congrFun h.2 1
    change X (-conj z) 1-X 1 1=X (conj z) 1-X 1 1 at v
    change X (conj z) 1-X 1 1= -(X z 1-X 1 1) at c
    rcases sides with x|x|y|y
    · apply axis (w:=-conj z) _ (v.trans c)
      rw [show -conj z=z by apply Complex.ext <;> simp [x]]
    · apply axis (w:=-conj z) _ (v.trans c)
      have e := per (-conj z) 2 L.ω₁_mem_lattice
      rw [show -conj z+2=z by apply Complex.ext <;> norm_num [x]] at e
      exact e.symm
    · apply axis (w:=conj z) _ c
      rw [show conj z=z by apply Complex.ext <;> simp [y]]
    · apply axis (w:=conj z) _ c
      have step : 2*I*(t:ℂ)∈L.lattice := (rhombic_mem_lattice_iff ht _).mpr ⟨-1,2,by norm_num,by simp⟩
      have e := per (conj z) _ step
      rw [show conj z+2*I*(t:ℂ)=z by apply Complex.ext <;> simp [y,Complex.mul_re,Complex.mul_im]; ring] at e
      exact e.symm

/-- Positive heights cannot approach the lower left puncture from the
open first quarter. This follows from the limit of the central saddle
arc at the interior abscissa a. -/
theorem quarter_positive_height_avoids_origin {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z) :
    ∀ᶠ z in 𝓝 (0:ℂ), z.re∈Ioo (0:ℝ) 1 → z.im∈Ioo (0:ℝ) t → X z 2<X 1 2 := by
  obtain ⟨r,graph,_,limit,_,_,_⟩ := actual_central_height_arc ht ha d per
  have above : ∀ᶠ y in 𝓝[>] (0:ℝ), a/2<r y := limit.eventually (Ioi_mem_nhds (half_lt_self ha.1))
  obtain ⟨δ,dp,cut⟩ := Metric.mem_nhdsWithin_iff.mp above
  have xx : ∀ᶠ z in 𝓝 (0:ℂ), z.re<a/2 := continuous_re.continuousAt.eventually (Iio_mem_nhds (half_pos ha.1))
  have yy : ∀ᶠ z in 𝓝 (0:ℂ), z.im∈ball 0 δ := continuous_im.continuousAt.eventually (ball_mem_nhds 0 dp)
  filter_upwards [xx,yy] with z small close
  intro x y
  have less : z.re<r z.im := small.trans (cut ⟨close,y.1⟩)
  have hit := ((graph z.im y).2 _ (graph _ y).1).mpr rfl
  have order := actual_quarter_height_row_strictMono ht y d (Ioo_subset_Icc_self x)
    (Ioo_subset_Icc_self (graph z.im y).1) less
  have id : ((z.re:ℝ):ℂ)+I*z.im=z := by apply Complex.ext <;> simp
  dsimp only at order
  rwa [id,hit] at order

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quarter_rectangle_punctures_and_axes
#print axioms TwoAxisHelicoid.quarter_positive_height_avoids_origin
