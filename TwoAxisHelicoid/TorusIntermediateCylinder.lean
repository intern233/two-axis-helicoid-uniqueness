import TwoAxisHelicoid.PuncturedDiskLogCover
import TwoAxisHelicoid.GenusOneUniformizationReduction
import TwoAxisHelicoid.EquivariantTorusFrame

namespace TwoAxisHelicoid
open Complex Set Function Topology
open scoped Topology ContDiff Manifold

/-- The covering plane of any topologically marked torus factors
through an actual open cylinder. Both the plane-to-cylinder covering
and the plane-to-torus covering are retained. -/
theorem topological_torus_intermediate_annulus {M : Type*} [TopologicalSpace M] {L : PeriodPair}
    (mark : M ≃ₜ PeriodTorus L) :
    let C := {z : ℂ // 0<‖z‖ ∧ ‖z‖<1}
    ∃ (a : ℂ → C) (b : C → M), IsCoveringMap a ∧ Surjective a ∧ IsLocalHomeomorph b ∧
      IsCoveringMap (b ∘ a) ∧ Surjective (b ∘ a) := by
  intro C
  obtain ⟨a,cov,onto,fib⟩ := punctured_disk_cyclic_plane_cover (R := 1) one_pos
  let t : ℂ := 2*(Real.pi:ℂ)*I
  have tn : t≠0 := mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  let k := L.basis 0/t
  have kn : k≠0 := div_ne_zero (L.basis.ne_zero 0) tn
  let J := Homeomorph.mulLeft₀ k kn
  let p := mark.symm ∘ periodTorusProjection L ∘ J
  have cover : IsCoveringMap p := ((periodTorusProjection_isCoveringMap L).comp_homeomorph J).homeomorph_comp mark.symm
  have sur : Surjective p := mark.symm.surjective.comp ((Quotient.mk_surjective :
    Surjective (periodTorusProjection L)).comp J.surjective)
  have identify (x y : ℂ) (eq : a x=a y) : p x=p y := by
    obtain ⟨n,hn⟩ := (fib x y).mp eq
    apply congrArg mark.symm
    have kt : k*t=L.basis 0 := div_mul_cancel₀ _ tn
    have step : J x=J y+n • L.basis 0 := by
      change k*x=k*y+n • L.basis 0
      rw [hn,← kt,zsmul_eq_mul]
      change k*(y+(n:ℂ)*t)=k*y+(n:ℂ)*(k*t)
      ring
    change periodTorusProjection L (J x)=periodTorusProjection L (J y)
    rw [step]
    exact periodTorusProjection_add_lattice L _ _ (L.lattice.smul_mem n (by rw [L.basis_zero]; exact L.ω₁_mem_lattice))
  let b := quotientFiberDescend a onto p
  have factor : b ∘ a=p := funext (quotientFiberDescend_apply a onto p identify)
  have fac : IsLocalHomeomorphOn (b ∘ a) univ := factor ▸ cover.isLocalHomeomorph.isLocalHomeomorphOn
  have loc := fac.of_comp_right (cov.isLocalHomeomorph.isLocalHomeomorphOn (s := univ))
  rw [image_univ,onto.range_eq] at loc
  exact ⟨a,b,cov,onto,isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr loc,factor ▸ cover,factor ▸ sur⟩

/-- A universal covering used as an intermediate presentation can
be replaced by a second simply connected covering of its base. -/
theorem replace_simply_connected_cover {P E B : Type*} [TopologicalSpace P] [TopologicalSpace E] [TopologicalSpace B]
    [SimplyConnectedSpace P] [LocallyPathConnectedSpace P] [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    {p : P → B} {q : E → B} (pc : IsCoveringMap p) (qc : IsCoveringMap q)
    (x : P) (y : E) (base : p x=q y) : ∃ H : P ≃ₜ E, q ∘ H=p := by
  let f : C(P,B) := ⟨p,pc.continuous⟩
  let g : C(E,B) := ⟨q,qc.continuous⟩
  obtain ⟨F,⟨vF,prF⟩,_⟩ := qc.existsUnique_continuousMap_lifts f x y base.symm
  obtain ⟨G,⟨vG,prG⟩,_⟩ := pc.existsUnique_continuousMap_lifts g y x base
  have l : G ∘ F=id := pc.eq_of_comp_eq (G.continuous.comp F.continuous) continuous_id
    (funext fun w => (congrFun prG (F w)).trans (congrFun prF w)) x ((congrArg G vF).trans vG)
  have r : F ∘ G=id := qc.eq_of_comp_eq (F.continuous.comp G.continuous) continuous_id
    (funext fun w => (congrFun prF (G w)).trans (congrFun prG w)) y ((congrArg F vG).trans vF)
  exact ⟨⟨⟨F,G,congrFun l,congrFun r⟩,F.continuous,G.continuous⟩,prF⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.topological_torus_intermediate_annulus
#print axioms TwoAxisHelicoid.replace_simply_connected_cover
