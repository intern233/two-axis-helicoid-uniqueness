import TwoAxisHelicoid.PhysicalMorseSaddleArcs
import Mathlib.Topology.UnitInterval

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology unitInterval

/-- The first Boolean selects the horizontal axis and the second its
positive direction, with the same sign convention on the vertical axis. -/
def saddleHalfAxis : Bool×Bool → ℝ → ℝ×ℝ
  | (true,true),t => (t,0)
  | (true,false),t => (-t,0)
  | (false,true),t => (0,t)
  | (false,false),t => (0,-t)

private theorem saddle_half_axis_bounds (i : Bool×Bool) {t r : ℝ} (ht : 0≤t) (hr : t≤r) :
    |(saddleHalfAxis i t).1|≤r ∧ |(saddleHalfAxis i t).2|≤r ∧
      (saddleHalfAxis i t).1*(saddleHalfAxis i t).2=0 := by
  obtain ⟨a,b⟩ := i
  cases a <;> cases b <;> simp [saddleHalfAxis,abs_of_nonneg ht,hr,ht.trans hr]

private theorem saddle_half_axis_rep {x y r : ℝ} (prod : x*y=0) (nz : (x,y)≠(0,0))
    (hx : |x|≤r) (hy : |y|≤r) : ∃ i t, 0<t ∧ t≤r ∧ saddleHalfAxis i t=(x,y) := by
  rcases mul_eq_zero.mp prod with ax|ay
  · subst x
    rcases lt_trichotomy y 0 with neg|zero|pos
    · exact ⟨(false,false),-y,neg_pos.mpr neg,(abs_of_neg neg) ▸ hy,by simp [saddleHalfAxis]⟩
    · exact (nz (by rw [zero])).elim
    · exact ⟨(false,true),y,pos,(abs_of_pos pos) ▸ hy,rfl⟩
  · subst y
    rcases lt_trichotomy x 0 with neg|zero|pos
    · exact ⟨(true,false),-x,neg_pos.mpr neg,(abs_of_neg neg) ▸ hx,by simp [saddleHalfAxis]⟩
    · exact (nz (by rw [zero])).elim
    · exact ⟨(true,true),x,pos,(abs_of_pos pos) ▸ hx,rfl⟩

/-- The four actual radial arcs start at the singular point, remain
in its physical level, and exhaust a relative punctured neighborhood.
Their other points are genuinely different from the saddle. -/
theorem saddle_level_has_four_half_arms {M : Type*} [TopologicalSpace M] {h : M → ℝ} {p : M}
    (e : OpenPartialHomeomorph M (ℝ×ℝ)) (src : p∈e.source) (center : e p=0)
    (model : ∀ᶠ x in 𝓝 p, h x=h p+(e x).1*(e x).2) :
    let P : h ⁻¹' {h p} := ⟨p,rfl⟩
    ∃ g : Bool×Bool → C(I,h ⁻¹' {h p}), (∀ i, g i 0=P) ∧
      (∀ i (t : I), 0<t → g i t≠P) ∧
      ∀ᶠ q in 𝓝 P, q≠P → ∃ (i : Bool×Bool) (t : I), 0<t ∧ g i t=q := by
  obtain ⟨r,rp,square⟩ := saddle_height_closed_coordinate_square e src center model
  let P : h ⁻¹' {h p} := ⟨p,rfl⟩
  let w := fun i (t : I) => saddleHalfAxis i (r*(t:ℝ))
  have bounds (i : Bool×Bool) (t : I) : |(w i t).1|≤r ∧ |(w i t).2|≤r ∧ (w i t).1*(w i t).2=0 :=
    saddle_half_axis_bounds _ (mul_nonneg rp.le t.2.1) (by simpa using mul_le_mul_of_nonneg_left t.2.2 rp.le)
  have target (i : Bool×Bool) (t : I) := (square (w i t) (bounds i t).1 (bounds i t).2.1).1
  have level (i : Bool×Bool) (t : I) : h (e.symm (w i t))=h p := by
    rw [(square (w i t) (bounds i t).1 (bounds i t).2.1).2,(bounds i t).2.2,add_zero]
  have cw (i : Bool×Bool) : Continuous (w i) := by
    obtain ⟨a,b⟩ := i
    cases a <;> cases b <;> dsimp [w,saddleHalfAxis] <;> fun_prop
  let g := fun i => (⟨fun t => ⟨e.symm (w i t),level i t⟩,
    (e.continuousOn_symm.comp_continuous (cw i) (target i)).subtype_mk _⟩ : C(I,h ⁻¹' {h p}))
  have zero (i : Bool×Bool) : w i 0=0 := by
    obtain ⟨a,b⟩ := i
    cases a <;> cases b <;> simp [w,saddleHalfAxis]
  refine ⟨g,fun i => Subtype.ext ?_,?_,?_⟩
  · change e.symm (w i 0)=p
    rw [zero,← center,e.left_inv src]
  · intro i t pos eq
    have coord := congrArg (fun q : h ⁻¹' {h p} => e q.1) eq
    change e (e.symm (w i t))=e p at coord
    rw [e.right_inv (target i t),center] at coord
    have nz : r*(t:ℝ)≠0 := (mul_pos rp (show 0<(t:ℝ) from pos)).ne'
    obtain ⟨a,b⟩ := i
    cases a <;> cases b <;> simp [w,saddleHalfAxis,nz] at coord
  have lim : Tendsto (fun q : h ⁻¹' {h p} => e q.1) (𝓝 P) (𝓝 0) :=
    center ▸ (e.continuousAt src).tendsto.comp continuous_subtype_val.continuousAt
  have nearX : ∀ᶠ q in 𝓝 P, |(e q.1).1|<r :=
    ((continuous_abs.comp continuous_fst).continuousAt.tendsto.comp lim).eventually (Iio_mem_nhds (by simpa using rp))
  have nearY : ∀ᶠ q in 𝓝 P, |(e q.1).2|<r :=
    ((continuous_abs.comp continuous_snd).continuousAt.tendsto.comp lim).eventually (Iio_mem_nhds (by simpa using rp))
  filter_upwards [nearX,nearY,continuous_subtype_val.continuousAt.eventually (e.open_source.mem_nhds src),
    continuous_subtype_val.continuousAt.eventually model] with q hx hy qs actual
  intro distinct
  have prod : (e q.1).1*(e q.1).2=0 := by linarith only [actual,(show h q.1=h p from q.2)]
  have nz : ((e q.1).1,(e q.1).2)≠(0,0) := fun eq => distinct (Subtype.ext (e.injOn qs src (eq.trans center.symm)))
  obtain ⟨i,d,dp,dr,repr⟩ := saddle_half_axis_rep prod nz hx.le hy.le
  let t : I := ⟨d/r,div_nonneg dp.le rp.le,(div_le_one rp).mpr dr⟩
  refine ⟨i,t,(show (0:ℝ)<d/r from div_pos dp rp),Subtype.ext ?_⟩
  change e.symm (saddleHalfAxis i (r*(d/r)))=q.1
  rw [show r*(d/r)=d by field_simp,repr,e.left_inv qs]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.saddle_level_has_four_half_arms
