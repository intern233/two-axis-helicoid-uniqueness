import TwoAxisHelicoid.EqualAngleMinimalContact
import TwoAxisHelicoid.ThreeArmsRealCoordinate

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric Function InnerProductSpace
open scoped Topology ContDiff

/-- The off-crossing case in the axis argument of Proposition 4.2.
If the intersection near a point lies in a set admitting an injective
real coordinate, distinct regular minimal sheet germs are transverse. -/
theorem distinct_minimal_sheets_transverse_on_line {X Y : ℂ → Fin 3 → ℝ} {a b : ℂ}
    (hx : ∀ᶠ z in 𝓝 a, (∀ j, HarmonicAt (fun w => X w j) z) ∧ ConformalCoordinateDerivatives X z)
    (hy : ∀ᶠ w in 𝓝 b, (∀ j, HarmonicAt (fun v => Y v j) w) ∧ ConformalCoordinateDerivatives Y w)
    (ix : Injective (fderiv ℝ X a)) (iy : Injective (fderiv ℝ Y b)) (meet : X a=Y b)
    (distinct : ¬ ∀ᶠ z in 𝓝 a, X z∈range Y)
    {V₀ : Set ℂ} (nbd : V₀∈𝓝 b) (line : Set (Fin 3 → ℝ)) (u : (Fin 3 → ℝ) → ℝ)
    (cu : Continuous u) (unique : InjOn u line)
    (intersection : ∀ᶠ z in 𝓝 a, X z∈Y '' V₀ → X z∈line) :
    (fderiv ℝ X a).range≠(fderiv ℝ Y b).range := by
  intro same
  obtain ⟨V,vb,sub,_,identical|⟨f,K,inj,cover,_,_⟩⟩ :=
    equal_angle_intersection_of_minimal_sheets hx hy ix iy meet same nbd
  · apply distinct
    obtain ⟨U,W,op,_,aa,_,_,_,_,_,images⟩ := identical univ univ_mem
    filter_upwards [op.mem_nhds aa] with z hz
    exact image_subset_range _ _ (images ▸ (show X z∈X '' U from mem_image_of_mem _ hz))
  · have contX : ∀ᶠ z in 𝓝 a, ContinuousAt X z := hx.mono (fun _ h =>
      (analyticAt_pi_iff.mpr (fun j => _root_.HarmonicAt.analyticAt (h.1 j))).continuousAt)
    obtain ⟨d,dp,good⟩ := Metric.mem_nhds_iff.mp (intersection.and contX)
    let r := min d K.radius / 2
    have rp : 0<r := half_pos (lt_min dp K.radius_pos)
    have rd : r<d := (half_lt_self (lt_min dp K.radius_pos)).trans_le (min_le_left _ _)
    have rk : r<K.radius := (half_lt_self (lt_min dp K.radius_pos)).trans_le (min_le_right _ _)
    let value := fun i s => u (X (K.arm i s))
    have distAt {s : ℝ} (hs : s∈Icc 0 r) (i) : dist (K.arm i s) a=s := (K.distance i s).trans (abs_of_nonneg hs.1)
    have ball {s : ℝ} (hs : s∈Icc 0 r) (i) : K.arm i s∈Metric.ball a d := by
      change dist (K.arm i s) a<d
      rw [distAt hs]
      exact hs.2.trans_lt rd
    have small {s : ℝ} (hs : s∈Icc 0 r) (i) : K.arm i s∈Metric.ball a K.radius :=
      show dist (K.arm i s) a<K.radius by rw [distAt hs]; exact hs.2.trans_lt rk
    have onLine {s : ℝ} (hs : s∈Icc 0 r) (i) : X (K.arm i s)∈line := by
      apply (good (ball hs i)).1
      apply image_mono sub
      rcases eq_or_lt_of_le hs.1 with zero|pos
      · rw [← zero,K.center]
        exact ⟨b,mem_of_mem_nhds vb,meet.symm⟩
      · apply (cover _ (by rwa [distAt hs]) (small hs i)).mpr
        exact ⟨i,by rw [distAt hs]⟩
    have continuous (i) : ContinuousOn (value i) (Icc 0 r) := by
      intro s hs
      exact (cu.continuousAt.comp (good (ball hs i)).2).comp_continuousWithinAt
        ((K.regular i).continuousOn.mono (show Icc 0 r⊆Ico 0 K.radius from fun t ht => ⟨ht.1,ht.2.trans_lt rk⟩) s hs)
    have beginMem : X a∈line := intersection.self_of_nhds ⟨b,mem_of_mem_nhds nbd,meet.symm⟩
    have zeroIn : a∈Metric.ball a K.radius := Metric.mem_ball_self K.radius_pos
    apply no_real_coordinate_on_three_arms (ι:=Fin (2*K.order)) (by simp; have := K.at_least_two; omega)
      rp value continuous (fun i => congrArg (u ∘ X) (K.center i))
    · intro i eq
      have last : r∈Icc 0 r := ⟨rp.le,le_rfl⟩
      have arm := inj (small last i) zeroIn (unique (onLine last i) beginMem eq)
      have dr := distAt last i
      rw [arm,dist_self] at dr
      exact rp.ne' dr.symm
    · intro i j s t hs ht eq
      have ls : s∈Icc 0 r := ⟨hs.1.le,hs.2⟩
      have lt' : t∈Icc 0 r := ⟨ht.1.le,ht.2⟩
      have sameArm := inj (small ls i) (small lt' j) (unique (onLine ls i) (onLine lt' j) eq)
      exact (K.separated i j s t ⟨hs.1,hs.2.trans_lt rk⟩ ⟨ht.1,ht.2.trans_lt rk⟩ sameArm).1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.distinct_minimal_sheets_transverse_on_line
