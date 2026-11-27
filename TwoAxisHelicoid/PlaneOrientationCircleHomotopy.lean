import TwoAxisHelicoid.PlaneOrientationCircleDegree

namespace TwoAxisHelicoid
open Function Set Filter Topology
open scoped Topology

/-- The circle degree is constant along a continuous real parameter family.
The simultaneous lift on the simply connected parameter/angle plane gives a
single integer increment for the entire family. -/
theorem orientationCircle_family_degree (K : ℝ × OrientationCircle → OrientationCircle)
    (hK : Continuous K) :
    ∃ n : ℤ, ∀ t : ℝ, HasOrientationCircleDegree (fun a => K (t,a)) n := by
  let π : ℝ → OrientationCircle := (↑)
  let g : C(ℝ × ℝ,OrientationCircle) :=
    ⟨fun a => K (a.1,π a.2),hK.comp (continuous_fst.prodMk (QuotientAddGroup.continuous_mk.comp continuous_snd))⟩
  obtain ⟨b,hb⟩ := (Quotient.mk_surjective : Surjective π) (g (0,0))
  obtain ⟨F,⟨_,hF⟩,_⟩ := (AddCircle.isCoveringMap_coe (1:ℝ)).existsUnique_continuousMap_lifts g (0,0) b hb
  have hl (a : ℝ × ℝ) : (F a : OrientationCircle) = K (a.1,π a.2) := congrFun hF a
  let G := fun a : ℝ × ℝ => F (a.1,a.2+1)
  have hG : Continuous G := F.continuous.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
  obtain ⟨n,hn⟩ := orientationCircle_lifts_difference hG F.continuous (fun a => by
    change (F (a.1,a.2+1) : OrientationCircle) = (F a : OrientationCircle)
    rw [hl,hl]
    change K (a.1,((a.2+1:ℝ):OrientationCircle)) = K (a.1,(a.2:OrientationCircle))
    rw [AddCircle.coe_add_period]) (0,0)
  exact ⟨n,fun t => ⟨fun x => F (t,x),F.continuous.comp (continuous_const.prodMk continuous_id),
    fun x => hl (t,x),fun x => hn (t,x)⟩⟩

theorem HasOrientationCircleDegree.family {K : ℝ × OrientationCircle → OrientationCircle}
    (hK : Continuous K) {s t : ℝ} {n : ℤ} (h : HasOrientationCircleDegree (fun a => K (s,a)) n) :
    HasOrientationCircleDegree (fun a => K (t,a)) n := by
  obtain ⟨m,hm⟩ := orientationCircle_family_degree K hK
  rw [h.unique (hm s)]
  exact hm t

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.orientationCircle_family_degree
