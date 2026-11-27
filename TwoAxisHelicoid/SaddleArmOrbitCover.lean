import TwoAxisHelicoid.FourSaddleHalfArms
import TwoAxisHelicoid.SingularOrbitBouquet

namespace TwoAxisHelicoid
open Set Filter Function Topology
open scoped Topology unitInterval OnePoint

/-- When all time parametrizations are open, every orbit of the action
is clopen in its regular space, including the periodic ones. -/
theorem clopen_range_of_open_time_action {Y : Type*} [TopologicalSpace Y] (Φ : ℝ → Y → Y)
    (start : ∀ x, Φ 0 x=x) (add : ∀ a b x, Φ (a+b) x=Φ a (Φ b x))
    (op : ∀ x, IsOpenMap (fun t => Φ t x)) (x : Y) : IsClopen (range (fun t => Φ t x)) := by
  refine ⟨isOpen_compl_iff.mp ?_,(op x).isOpen_range⟩
  apply isOpen_iff_forall_mem_open.mpr
  intro y outside
  refine ⟨range (fun t => Φ t y),?_,(op y).isOpen_range,0,start y⟩
  rintro _ ⟨t,rfl⟩ ⟨s,same⟩
  have eq := time_orbit_range_of_meeting Φ add same
  exact outside (eq.symm ▸ (show y∈range (fun u => Φ u y) from ⟨0,start y⟩))

/-- The four radial tips of a saddle meet every regular orbit of its
singular connected component. A punctured arm lies in just one open
orbit, and every regular trajectory tends back to the saddle. -/
theorem time_orbit_cover_of_finite_half_arms {Y ι : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    (p : Y) (Φ : ℝ → ({p}ᶜ : Set Y) → ({p}ᶜ : Set Y)) (start : ∀ x, Φ 0 x=x)
    (add : ∀ a b x, Φ (a+b) x=Φ a (Φ b x)) (cont : ∀ x, Continuous (fun t => Φ t x))
    (op : ∀ x, IsOpenMap (fun t => Φ t x)) (g : ι → C(I,Y)) (base : ∀ i, g i 0=p)
    (away : ∀ i (t : I), 0<t → g i t≠p)
    (near : ∀ᶠ q in 𝓝 p, q≠p → ∃ (i : ι) (t : I), 0<t ∧ g i t=q) :
    let seeds := fun i => (⟨g i 1,away i 1 zero_lt_one⟩ : ({p}ᶜ : Set Y))
    (∀ i, (seeds i).1∈connectedComponent p) ∧
      ∀ x : ({p}ᶜ : Set Y), x.1∈connectedComponent p → ∃ i t, Φ t (seeds i)=x := by
  let D := ({p}ᶜ : Set Y)
  let seeds := fun i => (⟨g i 1,away i 1 zero_lt_one⟩ : D)
  have inside (i : ι) : (seeds i).1∈connectedComponent p :=
    (isPreconnected_range (g i).continuous).subset_connectedComponent ⟨0,base i⟩ (mem_range_self 1)
  have alongArm (i : ι) (t : I) (pos : 0<t) :
      (⟨g i t,away i t pos⟩ : D)∈range (fun s => Φ s (seeds i)) := by
    let K := Ioc (0:ℝ) 1
    let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioc
    let a := fun s : K => (⟨s.1,s.2.1.le,s.2.2⟩ : I)
    have ca : Continuous a := continuous_subtype_val.subtype_mk _
    let path := fun s : K => (⟨g i (a s),away i (a s) s.2.1⟩ : D)
    have cp : Continuous path := ((g i).continuous.comp ca).subtype_mk _
    let last : K := ⟨1,zero_lt_one,le_rfl⟩
    have endMem : path last∈range (fun s => Φ s (seeds i)) := ⟨0,start _⟩
    have cl := (clopen_range_of_open_time_action Φ start add op (seeds i)).preimage cp
    have full := cl.eq_univ ⟨last,endMem⟩
    exact (show (⟨t.1,pos,t.2.2⟩ : K)∈path ⁻¹' range (fun s => Φ s (seeds i)) from full ▸ mem_univ _)
  refine ⟨inside,?_⟩
  intro x member
  obtain ⟨_,top,_⟩ := regular_orbit_in_singular_component p Φ start add cont op x member
  obtain ⟨s,hs⟩ := (top.eventually near).exists
  obtain ⟨i,t,pos,hit⟩ := hs (Φ s x).2
  obtain ⟨r,hr⟩ := alongArm i t pos
  have meet : Φ r (seeds i)=Φ s x := hr.trans (Subtype.ext hit)
  refine ⟨i,r-s,?_⟩
  rw [show r-s=(-s)+r by abel,add,meet,← add,neg_add_cancel,start]

/-- On the actual product-germ level, a marked nonlifting component
has an embedded compactified homoclinic orbit carrying its obstruction. -/
theorem obstructed_loop_of_saddle_height_action {M : Type*} [TopologicalSpace M] [T2Space M]
    {h : M → ℝ} {p : M} {v : ℝ} (hp : h p=v) [CompactSpace (h ⁻¹' {v})]
    (e : OpenPartialHomeomorph M (ℝ×ℝ)) (src : p∈e.source) (center : e p=0)
    (model : ∀ᶠ q in 𝓝 p, h q=h p+(e q).1*(e q).2)
    (H : C(M,Circle×Circle)) :
    let S := h ⁻¹' {v}
    let P : S := ⟨p,hp⟩
    let D := ({P}ᶜ : Set S)
    ∀ (Φ : ℝ → D → D), (∀ x, Φ 0 x=x) → (∀ a b x, Φ (a+b) x=Φ a (Φ b x)) →
      (∀ x, Continuous (fun t => Φ t x)) → (∀ x, IsOpenMap (fun t => Φ t x)) →
      (¬∃ u w : C(connectedComponent P,ℝ), ∀ q : connectedComponent P,
        normalizedPhase (u q)=(H q.1.1).1 ∧ normalizedPhase (w q)=(H q.1.1).2) →
      ∃ (x : D) (g : C(OnePoint ℝ,S)), x.1∈connectedComponent P ∧ g ∞=P ∧
        (∀ t : ℝ, g t=(Φ t x).1) ∧ Injective g ∧ ¬∃ u w : C(OnePoint ℝ,ℝ), ∀ t,
        normalizedPhase (u t)=(H (g t).1).1 ∧ normalizedPhase (w t)=(H (g t).1).2 := by
  subst v
  let S := h ⁻¹' {h p}
  let P : S := ⟨p,rfl⟩
  dsimp only
  intro Φ start add cont op fail
  obtain ⟨g,base,off,near⟩ := saddle_level_has_four_half_arms e src center model
  obtain ⟨belong,cover⟩ := time_orbit_cover_of_finite_half_arms P Φ start add cont op g base off near
  exact singular_component_obstructed_orbit P Φ start add cont op _ belong cover
    (H.comp ⟨Subtype.val,continuous_subtype_val⟩) fail

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.time_orbit_cover_of_finite_half_arms
#print axioms TwoAxisHelicoid.obstructed_loop_of_saddle_height_action
