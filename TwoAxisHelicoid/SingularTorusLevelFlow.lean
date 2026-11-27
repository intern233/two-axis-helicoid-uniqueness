import TwoAxisHelicoid.TorusActualLifts
import TwoAxisHelicoid.ActualTorusManifoldImmersion
import TwoAxisHelicoid.RegularLevelPlaneFlow
import TwoAxisHelicoid.RegularOrbitEndsAtSaddle
import TwoAxisHelicoid.EquivariantTorusFrame

namespace TwoAxisHelicoid
open Set Complex Filter Function Topology InnerProductSpace
open scoped ContDiff Topology

/-- Descent of a complete lattice-equivariant time action; the
two time laws remain true on the actual torus. -/
theorem complete_periodic_action_descends (L : PeriodPair) {Φ : ℝ → ℂ → ℂ}
    (start : ∀ z, Φ 0 z=z) (add : ∀ a b z, Φ (a+b) z=Φ a (Φ b z))
    (shift : ∀ t z w, w∈L.lattice → Φ t (z+w)=Φ t z+w) :
    ∃ A : ℝ → PeriodTorus L → PeriodTorus L, (∀ t z, A t (periodTorusProjection L z)=periodTorusProjection L (Φ t z)) ∧
      (∀ p, A 0 p=p) ∧ ∀ a b p, A (a+b) p=A a (A b p) := by
  let π := periodTorusProjection L
  have onto : Surjective π := Quotient.mk_surjective
  let A := fun t => quotientFiberDescend π onto (π ∘ Φ t)
  have act (t : ℝ) (z : ℂ) : A t (π z)=π (Φ t z) := by
    apply quotientFiberDescend_apply
    intro u w eq
    have lat := (periodTorusProjection_eq_iff L u w).mp eq
    calc π (Φ t u)=π (Φ t u+(w-u)) := (periodTorusProjection_add_lattice L _ _ lat).symm
         _=π (Φ t (u+(w-u))) := congrArg π (shift t u _ lat).symm
         _=π (Φ t w) := by rw [show u+(w-u)=w by abel]
  refine ⟨A,act,?_,?_⟩
  · intro p
    obtain ⟨z,rfl⟩ := onto p
    rw [act,start]
  · intro a b p
    obtain ⟨z,rfl⟩ := onto p
    rw [act,act,act,add]

private theorem orbit_in_torus_level_subspace (L : PeriodPair) {H : PeriodTorus L → ℝ} {v : ℝ}
    {D : Set (H ⁻¹' {v})} {γ : ℝ → ℂ} {G : ℝ → D}
    (level : ∀ t, H (periodTorusProjection L (γ t))=v) (cont : Continuous γ)
    (op : IsOpenMap (fun t => (⟨γ t,level t⟩ : (H ∘ periodTorusProjection L) ⁻¹' {v})))
    (projects : ∀ t, (G t).1.1=periodTorusProjection L (γ t)) : Continuous G ∧ IsOpenMap G := by
  let π := periodTorusProjection L
  let S := H ⁻¹' {v}
  let pr := S.restrictPreimage π
  let f := fun t => (⟨γ t,level t⟩ : (H ∘ π) ⁻¹' {v})
  have proj : Continuous π := QuotientAddGroup.continuous_mk
  have eq : (fun t => (G t).1)=pr ∘ f := funext (fun t => Subtype.ext (projects t))
  have cp : Continuous pr := (proj.comp continuous_subtype_val).subtype_mk _
  have co : Continuous (fun t => (G t).1) := eq.symm ▸ cp.comp (cont.subtype_mk _)
  have oo : IsOpenMap (fun t => (G t).1) := eq.symm ▸
    ((periodTorusProjection_isCoveringMap L).isOpenMap.restrictPreimage S).comp op
  exact ⟨co.subtype_mk _,oo.codRestrict (fun t => (G t).2)⟩

/-- At a level with one critical torus point there is a complete action
on its regular complement. On each orbit the physical plane trajectory
is C¹ with everywhere nonzero velocity. The level may contain a saddle. -/
theorem singular_torus_level_hamiltonian_action (L : PeriodPair) {H : PeriodTorus L → ℝ}
    (ch : Continuous H) {bad v : ℝ} (distinct : v≠bad)
    (smooth : ∀ z, H (periodTorusProjection L z)≠bad → ContDiffAt ℝ ∞ (H ∘ periodTorusProjection L) z)
    (p : H ⁻¹' {v}) (critical : ∀ z, H (periodTorusProjection L z)=v →
      ((∀ w, fderiv ℝ (H ∘ periodTorusProjection L) z w=0) ↔ periodTorusProjection L z=p.1)) :
    let D := ({p}ᶜ : Set (H ⁻¹' {v}))
    ∃ G : ℝ → D → D, (∀ x, G 0 x=x) ∧ (∀ a b x, G (a+b) x=G a (G b x)) ∧
      (∀ x, Continuous (fun t => G t x)) ∧ (∀ x, IsOpenMap (fun t => G t x)) ∧
      ∀ x, ∃ γ : ℝ → ℂ, ContDiff ℝ 1 γ ∧ (∀ t, deriv γ t≠0) ∧
        (∀ t, HasDerivAt γ (Complex.I*gradient (H ∘ periodTorusProjection L) (γ t)) t) ∧
        ∀ t, (G t x).1.1=periodTorusProjection L (γ t) := by
  let π := periodTorusProjection L
  let h := H ∘ π
  let D := ({p}ᶜ : Set (H ⁻¹' {v}))
  have onto : Surjective π := Quotient.mk_surjective
  have proj : Continuous π := QuotientAddGroup.continuous_mk
  have per (z w : ℂ) (hw : w∈L.lattice) : h (z+w)=h z := congrArg H (periodTorusProjection_add_lattice L z w hw)
  obtain ⟨Φ,start,add,shift,fixed,orbits⟩ := hamiltonian_flow_on_regular_part_of_level L (ch.comp proj) per distinct smooth
  obtain ⟨A,act,a0,aa⟩ := complete_periodic_action_descends L start add shift
  choose z lift using (fun x : D => onto x.1.1)
  have level (x : D) : h (z x)=v := (congrArg H (lift x)).trans x.1.2
  have off (x : D) : π (z x)≠p.1 := fun eq => x.2 (Subtype.ext ((lift x).symm.trans eq))
  have regular (x : D) : ∃ w, fderiv ℝ h (z x) w≠0 := by
    by_contra! zero
    exact off x ((critical _ (level x)).mp zero)
  choose allLevel sc speed physical eachOpen using (fun x : D => orbits (z x) (level x) (regular x))
  have stays (x : D) (t : ℝ) : π (Φ t (z x))≠p.1 := by
    intro atCritical
    have fixedHere := fixed _ (allLevel x t) ((critical _ (allLevel x t)).mpr atCritical) (-t)
    have back : Φ (-t) (Φ t (z x))=z x := by rw [← add,neg_add_cancel,start]
    exact off x ((congrArg π (back.symm.trans fixedHere)).trans atCritical)
  let G := fun t (x : D) => (⟨⟨π (Φ t (z x)),allLevel x t⟩,fun eq => stays x t (congrArg Subtype.val eq)⟩ : D)
  have rep (t : ℝ) (x : D) : (G t x).1.1=A t x.1.1 := by
    exact (act t (z x)).symm.trans (congrArg (A t) (lift x))
  have topo (x : D) := orbit_in_torus_level_subspace L (G:=fun t => G t x) (allLevel x) (sc x).continuous
    (eachOpen x) (fun _ => rfl)
  refine ⟨G,?_,?_,fun x => (topo x).1,fun x => (topo x).2,fun x => ⟨_,sc x,speed x,physical x,fun _ => rfl⟩⟩
  · intro x
    exact Subtype.ext (Subtype.ext ((rep 0 x).trans (a0 _)))
  · intro a b x
    apply Subtype.ext
    apply Subtype.ext
    rw [rep,rep,rep,aa]

theorem singular_torus_level_regular_action (L : PeriodPair) {H : PeriodTorus L → ℝ}
    (ch : Continuous H) {bad v : ℝ} (distinct : v≠bad)
    (smooth : ∀ z, H (periodTorusProjection L z)≠bad → ContDiffAt ℝ ∞ (H ∘ periodTorusProjection L) z)
    (p : H ⁻¹' {v}) (critical : ∀ z, H (periodTorusProjection L z)=v →
      ((∀ w, fderiv ℝ (H ∘ periodTorusProjection L) z w=0) ↔ periodTorusProjection L z=p.1)) :
    let D := ({p}ᶜ : Set (H ⁻¹' {v}))
    ∃ G : ℝ → D → D, (∀ x, G 0 x=x) ∧ (∀ a b x, G (a+b) x=G a (G b x)) ∧
      (∀ x, Continuous (fun t => G t x)) ∧ (∀ x, IsOpenMap (fun t => G t x)) ∧
      ∀ x, ∃ γ : ℝ → ℂ, ContDiff ℝ 1 γ ∧ (∀ t, deriv γ t≠0) ∧
        ∀ t, (G t x).1.1=periodTorusProjection L (γ t) := by
  obtain ⟨A,start,add,cont,op,orbits⟩ := singular_torus_level_hamiltonian_action L ch distinct smooth p critical
  refine ⟨A,start,add,cont,op,?_⟩
  intro x
  obtain ⟨γ,sc,speed,_,rep⟩ := orbits x
  exact ⟨γ,sc,speed,rep⟩

/-- A regular point on the singular component lies on an actual
nonperiodic plane trajectory. Its torus projection converges to the
specified singular point in both time directions. -/
theorem two_ended_regular_traversal_on_singular_torus_level (L : PeriodPair) {H : PeriodTorus L → ℝ}
    (ch : Continuous H) {bad v : ℝ} (distinct : v≠bad)
    (smooth : ∀ z, H (periodTorusProjection L z)≠bad → ContDiffAt ℝ ∞ (H ∘ periodTorusProjection L) z)
    (p : H ⁻¹' {v}) (critical : ∀ z, H (periodTorusProjection L z)=v →
      ((∀ w, fderiv ℝ (H ∘ periodTorusProjection L) z w=0) ↔ periodTorusProjection L z=p.1))
    (x : ({p}ᶜ : Set (H ⁻¹' {v}))) (same : x.1∈connectedComponent p) :
    ∃ γ : ℝ → ℂ, ContDiff ℝ 1 γ ∧ (∀ t, deriv γ t≠0) ∧ periodTorusProjection L (γ 0)=x.1.1 ∧
      Tendsto (periodTorusProjection L ∘ γ) atTop (𝓝 p.1) ∧ Tendsto (periodTorusProjection L ∘ γ) atBot (𝓝 p.1) ∧
      Injective (periodTorusProjection L ∘ γ) := by
  let S := H ⁻¹' {v}
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp (isClosed_singleton.preimage ch).isCompact
  obtain ⟨G,start,add,cont,op,curve⟩ := singular_torus_level_regular_action L ch distinct smooth p critical
  obtain ⟨emb,top,bot⟩ := regular_orbit_in_singular_component p G start add cont op x same
  obtain ⟨γ,sc,speed,rep⟩ := curve x
  have eq : (periodTorusProjection L ∘ γ)=(fun t => (G t x).1.1) := funext (fun t => (rep t).symm)
  refine ⟨γ,sc,speed,(rep 0).symm.trans (congrArg (fun y => y.1.1) (start x)),?_,?_,?_⟩
  · rw [eq]
    exact continuous_subtype_val.continuousAt.tendsto.comp top
  · rw [eq]
    exact continuous_subtype_val.continuousAt.tendsto.comp bot
  · intro s t equal
    exact emb.injective (Subtype.ext (Subtype.ext ((rep s).trans (equal.trans (rep t).symm))))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.singular_torus_level_regular_action
#print axioms TwoAxisHelicoid.two_ended_regular_traversal_on_singular_torus_level

#print axioms TwoAxisHelicoid.singular_torus_level_hamiltonian_action
