import TwoAxisHelicoid.CentralTorusHeightFiber
import TwoAxisHelicoid.CentralFiberProjectedArcs
import TwoAxisHelicoid.ExplicitMarkedReflections

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- The two central half-periods and the crossing of the two marked
axes are three different torus points. Their spatial positions lie
on the same transverse axis. The two outer positions are opposite
about the crossing, so one scalar tests their mutual separation. -/
theorem central_half_period_spatial_test {t a : ℝ} (ht : 0<t)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z) :
    let L := rhombicPeriodPair t ht
    let p : ℂ := (1+I*t)/2
    let q : ℂ := -conj p
    let δ := X p 1-X 1 1
    periodTorusProjection L p≠periodTorusProjection L q ∧
      periodTorusProjection L p≠periodTorusProjection L 1 ∧
      periodTorusProjection L q≠periodTorusProjection L 1 ∧
      X p-X 1=![0,δ,0] ∧ X q-X 1=![0,-δ,0] ∧
      (X p=X q ↔ δ=0) ∧ (X p=X 1 ↔ δ=0) := by
  intro L p q δ
  have pim : p.im=t/2 := by simp [p,div_ofNat_im]
  have pre : p.re=1/2 := by simp [p,div_ofNat_re]
  have inside : p.im∈Ioo 0 t := by rw [pim]; constructor <;> linarith
  have qi : q.im=p.im := by simp [q]
  have qr : q.re= -p.re := by simp [q]
  have off := rhombic_horizontal_strip_not_mem ht inside
  have fixed := per (-p) (1+I*t) L.ω₂_mem_lattice
  rw [show -p+(1+I*t)=p by dsimp [p]; ring] at fixed
  have flips := explicit_centered_primitive_reflections ht d per p off
  have cp : conj p∉L.lattice := fun m => off (by simpa using rhombic_conj_mem ht m)
  have half := (explicit_centered_primitive_reflections ht d per (conj p) cp).1
  have c := flips.2
  have sp : X p-X 1=![0,δ,0] := by
    have rev := flips.1
    change X (-p)-X 1= ![-(X p-X 1) 0,(X p-X 1) 1,-(X p-X 1) 2] at rev
    rw [← fixed] at rev
    funext j
    fin_cases j
    · have e := congrFun rev 0
      change X p 0-X 1 0= -(X p 0-X 1 0) at e
      change X p 0-X 1 0=0
      linarith
    · rfl
    · have e := congrFun rev 2
      change X p 2-X 1 2= -(X p 2-X 1 2) at e
      change X p 2-X 1 2=0
      linarith
  have sq : X q-X 1=![0,-δ,0] := by
    change X (conj p)-X 1= ![(X p-X 1) 0,-(X p-X 1) 1,-(X p-X 1) 2] at c
    change X q-X 1= ![-(X (conj p)-X 1) 0,(X (conj p)-X 1) 1,-(X (conj p)-X 1) 2] at half
    rw [c,sp] at half
    simpa using half
  have axis {z : ℂ} (iz : z.im∈Ioo 0 t) : periodTorusProjection L z≠periodTorusProjection L 1 := by
    intro e
    have m := (periodTorusProjection_eq_iff L _ _).mp e.symm
    exact (rhombic_horizontal_strip_not_mem ht (z:=z-1) (by change (z-1).im∈Ioo 0 t; simpa using iz)) m
  have distinct : periodTorusProjection L p≠periodTorusProjection L q := by
    intro e
    have eq := rhombic_centered_open_rectangle_inj ht (z:=p) (w:=q)
      (by rw [pre]; norm_num) inside (by rw [qr,pre]; norm_num) (qi.symm ▸ inside)
      ((periodTorusProjection_eq_iff L _ _).mp e.symm)
    have re := congrArg Complex.re eq
    linarith
  refine ⟨distinct,axis inside,axis (qi.symm ▸ inside),sp,sq,?_,?_⟩
  · constructor
    · intro e
      have a := congrFun sp 1
      have b := congrFun sq 1
      change X p 1-X 1 1=δ at a
      change X q 1-X 1 1= -δ at b
      rw [e] at a
      linarith
    · intro zero
      have e : X p-X 1=X q-X 1 := by rw [sp,sq,zero,neg_zero]
      exact sub_left_inj.mp e
  · constructor
    · intro e
      dsimp [δ]
      rw [e,sub_self]
    · intro zero
      apply sub_eq_zero.mp
      rw [sp,zero]
      funext j
      fin_cases j <;> rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_half_period_spatial_test
