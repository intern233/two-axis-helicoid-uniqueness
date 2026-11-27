import TwoAxisHelicoid.OneEndedPlaneLogarithm
import TwoAxisHelicoid.SimplyConnectedPlaneRiemannMap

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology
open scoped Topology ComplexConjugate

/-- A univalent unramified plane coordinate on a one-ended domain
has an analytic square root when its image omits zero. The avoidance
argument is applied in the image itself. -/
theorem one_ended_univalent_analytic_square_root {U : Set ℂ} (op : IsOpen U) (connected : IsConnected U)
    (tails : HasConnectedCompactTails U) {h : ℂ → ℂ} (hol : AnalyticOnNhd ℂ h U)
    (injective : InjOn h U) (regular : ∀ z∈U, deriv h z≠0) (nz : ∀ z∈U, h z≠0) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q U ∧ ∀ z∈U, q z^2=h z := by
  let g := U.domRestrict h
  have emb : IsOpenEmbedding g := by
    refine .of_continuous_injective_isOpenMap (continuousOn_iff_continuous_domRestrict.mp hol.continuousOn) injective.injective ?_
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    change 𝓝 (h x.1)≤map (h ∘ (Subtype.val : U → ℂ)) (𝓝 x)
    rw [← map_map,op.isOpenEmbedding_subtypeVal.map_nhds_eq x,(hol x.1 x.2).hasStrictDerivAt.map_nhds_eq (regular x.1 x.2)]
  have rangeEq : range g=h '' U := by
    ext x
    constructor
    · rintro ⟨w,m⟩
      exact ⟨w.1,w.2,m⟩
    · rintro ⟨w,m,eq⟩
      exact ⟨⟨w,m⟩,eq⟩
  have con : IsConnected (range g) := rangeEq ▸ connected.image h hol.continuousOn
  have miss : (0:ℂ)∉range g := fun ⟨z,e⟩ => nz z.1 z.2 e
  obtain ⟨Q,aq,eq⟩ := one_ended_plane_omitted_square_root emb.isOpen_range con
    (connected_compact_tails_homeomorph emb.toHomeomorph tails) miss
  have maps (z : ℂ) (hz : z∈U) : h z∈range g := ⟨⟨z,hz⟩,rfl⟩
  exact ⟨Q ∘ h,fun z hz => (aq _ (maps z hz)).comp (hol z hz),fun z hz => (eq _ (maps z hz)).trans (sub_zero _)⟩

/-- The disk-coordinate improvement on a one-ended plane domain.
An actual analytic square root supplies the factor through squaring. -/
theorem disk_coordinate_improves_on_one_ended_domain {U : Set ℂ} (op : IsOpen U) (connected : IsConnected U)
    (tails : HasConnectedCompactTails U) {p a : ℂ} (hp : p∈U) (ha : a∈complexUnitDisk) {f : ℂ → ℂ}
    (hf : NormalizedDiskCoordinate U p f) (skip : a∉f '' U) :
    ∃ g : ℂ → ℂ, NormalizedDiskCoordinate U p g ∧ ‖deriv f p‖<‖deriv g p‖ := by
  let h := diskMobius a ∘ f
  have hol : AnalyticOnNhd ℂ h U := fun z hz => (diskMobius_analyticAt ha (hf.maps hz)).comp (hf.analytic z hz)
  have no (z : ℂ) (hz : z∈U) : h z≠0 := by
    change (f z-a)/(1-conj a*f z)≠0
    exact div_ne_zero (sub_ne_zero.mpr (fun e => skip ⟨z,hz,e⟩)) (diskMobius_den_ne ha (hf.maps hz))
  have regH (z : ℂ) (hz : z∈U) : deriv h z≠0 := by
    rw [show deriv h z=deriv (diskMobius a) (f z)*deriv f z from
      deriv_comp z (diskMobius_analyticAt ha (hf.maps hz)).differentiableAt (hf.analytic z hz).differentiableAt]
    exact mul_ne_zero (diskMobius_regular ha (hf.maps hz)) (hf.regular z hz)
  obtain ⟨q,aq,square⟩ := one_ended_univalent_analytic_square_root op connected tails hol
    ((diskMobius_injOn ha).comp hf.injective hf.maps) regH no
  have mapq (z : ℂ) (hz : z∈U) : q z∈complexUnitDisk := by
    have sz : ‖q z‖^2<1 := by rw [← norm_pow,square _ hz]; exact mem_ball_zero_iff.mp (diskMobius_mapsTo ha (hf.maps hz))
    apply mem_ball_zero_iff.mpr
    nlinarith [norm_nonneg (q z)]
  let b := q p
  have hb : b∈complexUnitDisk := mapq p hp
  let g := diskMobius b ∘ q
  let B := fun w => diskMobius (-a) ((diskMobius (-b) w)^2)
  have sqMap : MapsTo (fun w : ℂ => w^2) complexUnitDisk complexUnitDisk := by
    intro w hw
    rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hw (by norm_num)
  have mb : MapsTo B complexUnitDisk complexUnitDisk :=
    (diskMobius_mapsTo (diskMobius_neg_mem ha)).comp (sqMap.comp (diskMobius_mapsTo (diskMobius_neg_mem hb)))
  have ab : AnalyticOnNhd ℂ B complexUnitDisk := fun w hw =>
    (diskMobius_analyticAt (diskMobius_neg_mem ha) (sqMap (diskMobius_mapsTo (diskMobius_neg_mem hb) hw))).comp (f:=fun z : ℂ => (diskMobius (-b) z)^2)
      ((diskMobius_analyticAt (diskMobius_neg_mem hb) hw).pow 2)
  have mg : MapsTo g U complexUnitDisk := fun _ hz => diskMobius_mapsTo hb (mapq _ hz)
  have ag : AnalyticOnNhd ℂ g U := fun z hz => (diskMobius_analyticAt hb (mapq z hz)).comp (aq z hz)
  have back (z : ℂ) (hz : z∈U) : B (g z)=f z := by
    dsimp only [B,g,Function.comp_apply]
    rw [diskMobius_inverse hb (mapq z hz),square z hz]
    exact diskMobius_inverse ha (hf.maps hz)
  have origin : g p=0 := by simp [g,b,diskMobius]
  have b0 : B 0=0 := (congrArg B origin.symm).trans ((back p hp).trans hf.origin)
  have collision : ¬InjOn B complexUnitDisk := by
    intro injective
    let d : ℂ := (1/2:ℝ)
    have hd : d∈complexUnitDisk := by norm_num [d,mem_ball_zero_iff]
    have nd := diskMobius_neg_mem hd
    have e : B (diskMobius b d)=B (diskMobius b (-d)) := by
      simp only [B,diskMobius_inverse hb hd,diskMobius_inverse hb nd,neg_sq]
    have impossible := diskMobius_injOn hb hd nd (injective (diskMobius_mapsTo hb hd) (diskMobius_mapsTo hb nd) e)
    norm_num [d] at impossible
  have strict := schwarz_strict_of_not_injective ab mb b0 collision
  have chain (z : ℂ) (hz : z∈U) : deriv f z=deriv B (g z)*deriv g z := by
    have loc : B ∘ g =ᶠ[𝓝 z] f := by filter_upwards [op.mem_nhds hz] with w hw using back w hw
    rw [← loc.deriv_eq,deriv_comp z (ab _ (mg hz)).differentiableAt (ag _ hz).differentiableAt]
  have reg (z : ℂ) (hz : z∈U) : deriv g z≠0 := fun e => hf.regular z hz ((chain z hz).trans (by rw [e,mul_zero]))
  refine ⟨g,⟨ag,mg,fun x hx y hy eq => hf.injective hx hy ((back x hx).symm.trans ((congrArg B eq).trans (back y hy))),origin,reg⟩,?_⟩
  rw [chain p hp,norm_mul,origin]
  simpa only [one_mul] using mul_lt_mul_of_pos_right strict (norm_pos_iff.mpr (reg p hp))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.one_ended_univalent_analytic_square_root
#print axioms TwoAxisHelicoid.disk_coordinate_improves_on_one_ended_domain
