import TwoAxisHelicoid.TorusFundamentalGenerators
import TwoAxisHelicoid.PeriodTorusComplexManifold
import TwoAxisHelicoid.CompactPunctureHomeomorphism

namespace TwoAxisHelicoid
open Complex Set Topology

/-- A nontrivial loop cannot be the image of a closed plane loop under a
continuous map. Both basepoints are recorded by the fundamental group map. -/
private theorem torus_generator_not_plane_image (L : PeriodPair) (P : C(ℂ,PeriodTorus L))
    (f : C(unitInterval,ℂ)) (hloop : f 1 = f 0)
    (hmap : ∀ s, P (f s) = (puncturedTorusGeneratorLoop L 0 s).1) : False := by
  let γ := puncturedTorusGeneratorLoop L 0
  let β : Path (f 0) (f 0) := ⟨f,rfl,hloop⟩
  have hb : P (f 0) = (puncturedTorusCenter L).1 := (hmap 0).trans (congrArg Subtype.val γ.source)
  let D := FundamentalGroup.mapOfEq P hb
  let g : FundamentalGroup ℂ (f 0) := .fromPath (.mk β)
  have he : D g = periodTorusGeneratorClass L 0 := by
    change FundamentalGroup.mapOfEq P hb (FundamentalGroup.fromPath (.mk β)) = _
    rw [FundamentalGroup.mapOfEq_apply]
    apply congrArg FundamentalGroup.fromPath
    apply congrArg Path.Homotopic.Quotient.mk
    ext s
    exact hmap s
  have hg : g = 1 := Subsingleton.elim .. 
  have hc := periodTorusGeneratorClass_coordinates L 0
  rw [← he,hg,map_one,map_one,ite_eq_left rfl] at hc
  have ht := congrArg (fun x : Multiplicative (ℤ × ℤ) => x.toAdd.1) hc
  norm_num at ht

/-- A punctured torus admits no height-translating homeomorphism. An
iterate of an essential loop would lie wholly in one puncture chart and
hence would be a closed plane loop. The inverse iterate extends across
the puncture, preserving the essential class in the compact torus. -/
theorem punctured_torus_no_height_translating_homeomorphism (L : PeriodPair)
    (e : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus L) (h : PuncturedPeriodTorus L → ℝ)
    (hc : Continuous h) {d : ℝ} (hd : d ≠ 0) (he : ∀ q, h (e q) = h q+d) : False := by
  classical
  let := periodTorus_compactSpace L
  let : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  let χ := periodTorusInverseChart L 0
  have hχ : (0:PeriodTorus L) ∈ χ.target := periodTorusInverseChart_target L 0
  let K : Set (PuncturedPeriodTorus L) := Subtype.val ⁻¹' χ.targetᶜ
  have hk : IsCompact K := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    have hK : Subtype.val '' K = χ.targetᶜ := by
      ext y
      constructor
      · rintro ⟨q,hy,rfl⟩; exact hy
      · intro hy
        exact ⟨⟨y,fun eq => hy (eq ▸ hχ)⟩,hy,rfl⟩
    rw [hK]
    exact χ.open_target.isClosed_compl.isCompact
  let γ := puncturedTorusGeneratorLoop L 0
  obtain ⟨B,hB⟩ := hk.bddAbove_image hc.abs.continuousOn
  obtain ⟨A,hA⟩ := (isCompact_range γ.continuous).bddAbove_image hc.abs.continuousOn
  obtain ⟨n,hn⟩ := exists_nat_gt ((A+B)/|d|)
  have hbig := (div_lt_iff₀ (abs_pos.mpr hd)).mp hn
  let E : ℕ → (PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus L) :=
    Nat.rec (Homeomorph.refl _) (fun _ F => F.trans e)
  have hstep (m : ℕ) (q : PuncturedPeriodTorus L) : h (E m q) = h q+(m:ℝ)*d := by
    induction m with
    | zero => simp [E]
    | succ m ih =>
      change h (e (E m q)) = _
      rw [he,ih,Nat.cast_succ]
      ring
  have hchart (s : unitInterval) : (E n (γ s)).1 ∈ χ.target := by
    by_contra hn
    have hb := hB (mem_image_of_mem _ (show E n (γ s) ∈ K from hn))
    have ha := hA (mem_image_of_mem _ (mem_range_self s))
    have heq : h (E n (γ s))-h (γ s) = (n:ℝ)*d := by rw [hstep]; ring
    have hsub := abs_sub (h (E n (γ s))) (h (γ s))
    rw [heq,abs_mul,abs_of_nonneg (Nat.cast_nonneg n)] at hsub
    linarith
  let f : C(unitInterval,ℂ) :=
    ⟨fun s => χ.symm (E n (γ s)).1,χ.continuousOn_symm.comp_continuous
      ((continuous_subtype_val.comp (E n).continuous).comp γ.continuous) hchart⟩
  let P : C(ℂ,PeriodTorus L) := ⟨compactPunctureExtension (E n).symm ∘ periodTorusProjection L,
    (compactPunctureExtension (E n).symm).continuous.comp QuotientAddGroup.continuous_mk⟩
  apply torus_generator_not_plane_image L P f
  · change χ.symm (E n (γ 1)).1 = χ.symm (E n (γ 0)).1
    rw [γ.target,γ.source]
  · intro s
    change compactPunctureExtension (E n).symm (periodTorusProjection L (χ.symm (E n (γ s)).1)) = (γ s).1
    rw [← periodTorusInverseChart_eq L 0,χ.right_inv (hchart s),compactPunctureExtension_apply,
      (E n).symm_apply_apply]

/-- In particular no Euclidean screw motion of nonzero vertical step can
preserve the image of an actual embedded once-punctured torus. -/
theorem punctured_torus_embedded_image_has_no_screw_period (L : PeriodPair)
    (X : PuncturedPeriodTorus L → Fin 3 → ℝ) (hX : IsEmbedding X)
    (s : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) {d : ℝ} (hd : d ≠ 0) (hs : ∀ v, s v 2 = v 2+d) :
    s '' range X ≠ range X := by
  intro H
  let S := range X
  let σ := (s.isEmbedding.homeomorphImage S).trans (Homeomorph.setCongr H)
  let E := (hX.toHomeomorph.trans σ).trans hX.toHomeomorph.symm
  have hmap (q : PuncturedPeriodTorus L) : X (E q) = s (X q) := by
    have h' := hX.toHomeomorph.apply_symm_apply (σ (hX.toHomeomorph q))
    exact congrArg Subtype.val h'
  exact punctured_torus_no_height_translating_homeomorphism L E (fun q => X q 2)
    ((continuous_apply 2).comp hX.continuous) hd (fun q => (congrFun (hmap q) 2).trans (hs (X q)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_torus_embedded_image_has_no_screw_period
