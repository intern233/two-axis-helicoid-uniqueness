import TwoAxisHelicoid.RhombicSlopingSquare
import TwoAxisHelicoid.CertifiedAxisCollisionCore

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ComplexConjugate

/-- The actual projected sloping generator and its conjugate on the
punctured parameter torus. -/
def rhombicSlopingCycle {t : ℝ} (ht : 0<t) (reflected : Bool) :
    Set (PuncturedPeriodTorus (rhombicPeriodPair t ht)) :=
  Subtype.val ⁻¹' ((fun s : ℝ => periodTorusProjection _ (if reflected then conj (originalPeriodPath t s)
    else originalPeriodPath t s)) '' Icc (-1) 1)

theorem rhombicSlopingCycle_closed {t : ℝ} (ht : 0<t) (b : Bool) :
    IsClosed (rhombicSlopingCycle ht b) := by
  let L := rhombicPeriodPair t ht
  let _ : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  have f : Continuous (originalPeriodPath t) := by unfold originalPeriodPath; fun_prop
  have proj : Continuous (periodTorusProjection L) := QuotientAddGroup.continuous_mk
  unfold rhombicSlopingCycle
  apply IsClosed.preimage continuous_subtype_val
  apply IsCompact.isClosed
  apply isCompact_Icc.image
  cases b
  · exact proj.comp f
  · exact proj.comp (continuous_conj.comp f)

private theorem sloping_square_edge_mem {t : ℝ} (ht : 0<t) (b : Bool) {s : ℝ}
    (hs : s∈Ico (0:ℝ) 1) {q : PuncturedPeriodTorus (rhombicPeriodPair t ht)}
    (e : periodTorusProjection _ (rhombicSlopingPoint t (if b then 0 else s) (if b then s else 0))=q.1) :
    q∈rhombicSlopingCycle ht b := by
  let L := rhombicPeriodPair t ht
  let edge := fun r : ℝ => rhombicSlopingPoint t (if b then 0 else r) (if b then r else 0)
  let path := fun u : ℝ => if b then conj (originalPeriodPath t u) else originalPeriodPath t u
  have line (r : ℝ) : path (2*r)=edge r := by
    cases b <;> simp [path,edge,originalPeriodPath,rhombicSlopingPoint,map_ofNat] <;> ring
  by_cases low : s≤1/2
  · exact ⟨2*s,⟨by linarith [hs.1],by linarith⟩,(congrArg (periodTorusProjection L) (line s)).trans e⟩
  · refine ⟨2*(s-1),⟨by linarith,by linarith [hs.2]⟩,?_⟩
    change periodTorusProjection L (path (2*(s-1)))=q.1
    rw [line]
    apply Eq.trans _ e
    apply (periodTorusProjection_eq_iff L _ _).mpr
    apply (rhombic_sloping_generator_basis ht _).mpr
    cases b
    · refine ⟨1,0,?_⟩
      simp [edge,rhombicSlopingPoint]
      ring
    · refine ⟨0,1,?_⟩
      simp [edge,rhombicSlopingPoint]
      ring

private theorem sloping_real_axis_mem {t : ℝ} (ht : 0<t) {q : PuncturedPeriodTorus (rhombicPeriodPair t ht)}
    (x : ℝ) (h : periodTorusProjection _ (x:ℂ)=q.1) : q∈rhombicMarkedAxes t ht := by
  let k : ℤ := ⌊x/2⌋
  let r := x-2*k
  have lb : 0≤r := by dsimp [r,k]; linarith [Int.floor_le (x/2)]
  have ub : r≤2 := by dsimp [r,k]; linarith [Int.lt_floor_add_one (x/2)]
  refine Or.inl ⟨r,⟨lb,ub⟩,Eq.trans ?_ h⟩
  apply (periodTorusProjection_eq_iff _ _ _).mpr
  apply (rhombic_mem_lattice_iff ht _).mpr
  exact ⟨k,0,by simp [r],by simp⟩

/-- Every punctured torus point off the two axes and the two sloping
cycles has a representative in one of four open triangles. The reflected
representatives range over one fixed triangle in the same marked lattice. -/
theorem rhombic_axis_cycle_complement_triangle {t : ℝ} (ht : 0<t) (q : PuncturedPeriodTorus (rhombicPeriodPair t ht))
    (off : q∉rhombicMarkedAxes t ht ∪ rhombicSlopingCycle ht false ∪ rhombicSlopingCycle ht true) :
    ∃ (z : ℂ) (x y : ℝ), periodTorusProjection _ z=q.1 ∧ 0<y ∧ y<x ∧ x+y<1 ∧
      (rhombicSlopingPoint t x y=z ∨ rhombicSlopingPoint t x y=conj z ∨
        rhombicSlopingPoint t x y= -z ∨ rhombicSlopingPoint t x y= -conj z) := by
  let L := rhombicPeriodPair t ht
  obtain ⟨w,eq⟩ := Quotient.exists_rep q.1
  change periodTorusProjection L w=q.1 at eq
  obtain ⟨u,hu,v,hv,lat⟩ := rhombic_sloping_square_rep ht w
  let z := rhombicSlopingPoint t u v
  have rep : periodTorusProjection L z=q.1 := ((periodTorusProjection_eq_iff L _ _).mpr lat).trans eq
  have up : 0<u := hu.1.lt_of_ne (by
    intro h
    exact off (Or.inr (sloping_square_edge_mem ht true hv (by simpa [z,← h] using rep))))
  have vp : 0<v := hv.1.lt_of_ne (by
    intro h
    exact off (Or.inl (Or.inr (sloping_square_edge_mem ht false hu (by simpa [z,← h] using rep)))))
  have diag : u≠v := by
    intro h
    have rz : z=((z.re:ℝ):ℂ) := Complex.ext rfl (by rw [(rhombicSlopingPoint_parts ..).2,h,sub_self,zero_mul,ofReal_im])
    exact off (Or.inl (Or.inl (sloping_real_axis_mem ht z.re ((congrArg (periodTorusProjection L) rz.symm).trans rep))))
  have cross : u+v≠1 := by
    intro h
    have zr : z.re=0 := by rw [(rhombicSlopingPoint_parts ..).1]; linarith
    have bounds : z.im∈Icc (-t) t := by
      rw [(rhombicSlopingPoint_parts ..).2]
      constructor
      · nlinarith [mul_le_mul_of_nonneg_right (show -1≤v-u by linarith [hu.2]) ht.le]
      · nlinarith [mul_le_mul_of_nonneg_right (show v-u≤1 by linarith [hv.2]) ht.le]
    apply off
    left; left; right
    have mark {k : ℝ} (p : 1+I*k∈L.lattice) (bd : z.im+k∈Icc (-t) t) :
        q.1∈ (fun r : ℝ => periodTorusProjection L (1+I*r)) '' Icc (-t) t := by
      refine ⟨z.im+k,bd,?_⟩
      change periodTorusProjection L (1+I*(z.im+k:ℝ))=q.1
      rw [show (1:ℂ)+I*(z.im+k:ℝ)=z+(1+I*k) by apply Complex.ext <;> simp [zr]]
      exact (periodTorusProjection_add_lattice L _ _ p).trans rep
    rcases le_total z.im 0 with neg|pos
    · exact mark L.ω₂_mem_lattice ⟨by linarith [bounds.1],by linarith⟩
    · have p : (1:ℂ)+I*(-t:ℝ)∈L.lattice := by
        apply (rhombic_sloping_generator_basis ht _).mpr
        refine ⟨1,0,?_⟩
        push_cast
        ring
      exact mark p ⟨by linarith,by linarith [bounds.2]⟩
  obtain ⟨x,y,py,xy,b,which⟩ := rhombic_sloping_open_triangle (t:=t) ⟨up,hu.2⟩ ⟨vp,hv.2⟩ diag cross
  exact ⟨z,x,y,rep,py,xy,b,which⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_axis_cycle_complement_triangle
