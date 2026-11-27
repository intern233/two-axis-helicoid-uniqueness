import TwoAxisHelicoid.PuncturedCoverExtension

namespace TwoAxisHelicoid
open Set Topology

theorem puncturedLatticePlane_add_lattice (L : PeriodPair)
    (z : PuncturedLatticePlane L) (ω₀ : L.lattice) : z.1+ω₀.1 ∉ L.lattice := by
  intro h
  apply z.2
  simpa only [add_sub_cancel_right] using L.lattice.sub_mem h ω₀.2

/-- A map over the base from the punctured flat sign cover to any cover
of the complete torus extends uniquely over the missing fiber. In
particular this does not assume the desired extension as spin data. -/
theorem puncturedSignCoverMap_extends (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    {E : Type*} [TopologicalSpace E] {p : E → PeriodTorus L} (hp : IsCoveringMap p)
    (f : C(PuncturedSignCover L χ,E))
    (hf : ∀ q, p (f q) = latticeSignCoverProjection L χ q.1) :
    ∃! F : C(LatticeSignCover L χ,E),
      (∀ q, p (F q) = latticeSignCoverProjection L χ q) ∧
      ∀ q : PuncturedSignCover L χ, F q.1 = f q := by
  classical
  let s (σ : ZMod 2) : C(PuncturedLatticePlane L,E) :=
    ⟨fun z => f (puncturedSignCoverMk L χ (z,σ)),
      f.continuous.comp ((puncturedSignCoverMk_continuous L χ).comp
        (continuous_id.prodMk continuous_const))⟩
  have hs (σ : ZMod 2) (z : PuncturedLatticePlane L) :
      p (s σ z) = periodTorusProjection L z.1 := hf _
  choose G hG using fun σ => (puncturedPlane_cover_lift_extends L hp (s σ) (hs σ)).exists
  let g : ℂ × ZMod 2 → E := fun v => G v.2 v.1
  have hc : Continuous g := by
    rw [continuous_prod_of_discrete_right]
    exact fun σ => (G σ).continuous
  have hgproj (v : ℂ × ZMod 2) : p (g v) = periodTorusProjection L v.1 := (hG v.2).1 v.1
  have hgreg (z : PuncturedLatticePlane L) (σ : ZMod 2) :
      g (z.1,σ) = f (puncturedSignCoverMk L χ (z,σ)) := (hG σ).2 z
  let z₀ : PuncturedLatticePlane L := puncturedBasisLine L 0 0
  have hgfiber (v w : ℂ × ZMod 2)
      (he : latticeSignCoverMk L χ v = latticeSignCoverMk L χ w) : g v = g w := by
    obtain ⟨ω₀,hω,hχ⟩ := (latticeSignCoverMk_eq L χ v w).mp he
    let z₁ : PuncturedLatticePlane L :=
      ⟨z₀.1+ω₀.1,puncturedLatticePlane_add_lattice L z₀ ω₀⟩
    have hz : puncturedSignCoverMk L χ (z₁,v.2) = puncturedSignCoverMk L χ (z₀,w.2) := by
      apply (puncturedSignCoverMk_eq L χ _ _).mpr
      exact ⟨ω₀,by simp [z₁],hχ⟩
    have he0 : g (z₀.1+ω₀.1,v.2) = g (z₀.1,w.2) := by
      rw [hgreg z₁ v.2,hgreg z₀ w.2,hz]
    have hh : (fun z : ℂ => g (z+ω₀.1,v.2)) = fun z => g (z,w.2) := by
      apply hp.eq_of_comp_eq
        ((G v.2).continuous.comp (continuous_id.add continuous_const)) (G w.2).continuous
        (funext fun z => ?_) z₀.1 he0
      change p (g (z+ω₀.1,v.2)) = p (g (z,w.2))
      rw [hgproj,hgproj,
        periodTorusProjection_add_lattice L z ω₀.1 ω₀.2]
    have hv : v.1 = w.1+ω₀.1 := (sub_eq_iff_eq_add.mp hω).trans (add_comm _ _)
    change g (v.1,v.2) = g (w.1,w.2)
    rw [hv]
    exact congrFun hh w.1
  let F : C(LatticeSignCover L χ,E) :=
    ⟨quotientFiberDescend (latticeSignCoverMk L χ) Quotient.mk_surjective g,
      quotientFiberDescend_continuous (QuotientAddGroup.isQuotientMap_mk (latticeSignGraph L χ))
        g hgfiber hc⟩
  have hFmk (v : ℂ × ZMod 2) : F (latticeSignCoverMk L χ v) = g v :=
    quotientFiberDescend_apply _ _ g hgfiber v
  have hFp (q : LatticeSignCover L χ) : p (F q) = latticeSignCoverProjection L χ q := by
    obtain ⟨v,rfl⟩ := Quotient.exists_rep q
    change p (F (latticeSignCoverMk L χ v)) = periodTorusProjection L v.1
    rw [hFmk,hgproj]
  have hFr (q : PuncturedSignCover L χ) : F q.1 = f q := by
    obtain ⟨v,rfl⟩ := puncturedSignCoverMk_surjective L χ q
    exact (hFmk (v.1.1,v.2)).trans (hgreg v.1 v.2)
  refine ⟨F,⟨hFp,hFr⟩,?_⟩
  intro H hH
  apply ContinuousMap.ext
  intro q
  obtain ⟨v,rfl⟩ := Quotient.exists_rep q
  have hcont : Continuous (fun z : ℂ => latticeSignCoverMk L χ (z,v.2)) :=
    QuotientAddGroup.continuous_mk.comp (continuous_id.prodMk continuous_const)
  have he : (fun z : ℂ => H (latticeSignCoverMk L χ (z,v.2))) =
      fun z => F (latticeSignCoverMk L χ (z,v.2)) := by
    apply hp.eq_of_comp_eq (H.continuous.comp hcont) (F.continuous.comp hcont)
      (funext fun z => (hH.1 _).trans (hFp _).symm) z₀.1
    exact (hH.2 (puncturedSignCoverMk L χ (z₀,v.2))).trans
      (hFr (puncturedSignCoverMk L χ (z₀,v.2))).symm
  exact congrFun he v.1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.puncturedSignCoverMap_extends
