import TwoAxisHelicoid.DiskMobiusDistance
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology
open scoped Topology ComplexConjugate

/-- The normalized coordinate maps used in the extremal construction
on a simply connected plane domain. -/
structure NormalizedDiskCoordinate (U : Set ℂ) (p : ℂ) (f : ℂ → ℂ) : Prop where
  analytic : AnalyticOnNhd ℂ f U
  maps : MapsTo f U complexUnitDisk
  injective : InjOn f U
  origin : f p=0
  regular : ∀ x∈U, deriv f x≠0

theorem diskMobius_injOn {a : ℂ} (ha : a∈complexUnitDisk) : InjOn (diskMobius a) complexUnitDisk :=
  fun _ hx _ hy eq => (diskMobius_inverse ha hx).symm.trans ((congrArg (diskMobius (-a)) eq).trans (diskMobius_inverse ha hy))

theorem diskMobius_regular {a z : ℂ} (ha : a∈complexUnitDisk) (hz : z∈complexUnitDisk) : deriv (diskMobius a) z≠0 := by
  have inv : diskMobius (-a) ∘ diskMobius a =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using diskMobius_inverse ha hw
  have eq := inv.deriv_eq
  rw [deriv_id,deriv_comp z (diskMobius_analyticAt (diskMobius_neg_mem ha) (diskMobius_mapsTo ha hz)).differentiableAt
    (diskMobius_analyticAt ha hz).differentiableAt] at eq
  exact fun h => one_ne_zero (eq.symm.trans (by rw [h,mul_zero]))

/-- Every continuous square root of a holomorphic nonzero function on
an open set is holomorphic in its given branch. -/
theorem analytic_continuous_square_root {U : Set ℂ} (op : IsOpen U) {q h : ℂ → ℂ}
    (cq : ContinuousOn q U) (ah : AnalyticOnNhd ℂ h U) (square : ∀ z∈U, (q z)^2=h z)
    (non : ∀ z∈U, h z≠0) : AnalyticOnNhd ℂ q U := by
  intro x hx
  let sq := fun z : ℂ => z^2
  have aq : AnalyticAt ℂ sq (q x) := analyticAt_id.pow 2
  have nq : q x≠0 := fun zero => non x hx ((square x hx).symm.trans (by rw [zero]; norm_num))
  have ds : deriv sq (q x)≠0 := by simp [sq,nq]
  let inv := aq.hasStrictDerivAt.localInverse _ _ _ ds
  have atx : sq (q x)=h x := square x hx
  have ai : AnalyticAt ℂ inv (h x) := atx ▸ aq.analyticAt_localInverse ds
  apply (ai.comp (ah x hx)).congr
  filter_upwards [(cq.continuousAt (op.mem_nhds hx)).eventually (aq.hasStrictDerivAt.eventually_left_inverse ds),
    op.mem_nhds hx] with z left hz
  change inv (h z)=q z
  rw [← square z hz]
  exact left

/-- A disk self-map fixing zero and identifying two distinct interior
points has derivative of norm strictly less than one. -/
theorem schwarz_strict_of_not_injective {B : ℂ → ℂ} (ab : AnalyticOnNhd ℂ B complexUnitDisk)
    (mb : MapsTo B complexUnitDisk complexUnitDisk) (zero : B 0=0) (collide : ¬ InjOn B complexUnitDisk) :
    ‖deriv B 0‖<1 := by
  have inside : MapsTo B complexUnitDisk (closedBall (B 0) 1) := by
    rw [zero]
    exact fun _ h => ball_subset_closedBall (mb h)
  apply lt_of_le_of_ne (norm_deriv_le_one_of_mapsTo_ball ab.differentiableOn inside zero_lt_one)
  intro eq
  have aff := affine_of_mapsTo_ball_of_norm_dslope_eq_div ab.differentiableOn inside (mem_ball_self zero_lt_one)
    (by simpa using eq)
  have nr : deriv B 0≠0 := fun h => one_ne_zero (eq.symm.trans (by rw [h,norm_zero]))
  apply collide
  intro x hx y hy ex
  have e := (aff hx).symm.trans (ex.trans (aff hy))
  simpa [zero,smul_eq_mul,nr] using e

/-- A disk coordinate which omits an interior value can be improved at
the marked point. The inverse factor is a disk map conjugate on the
two sides to squaring, so strict Schwarz supplies the improvement. -/
theorem disk_coordinate_improves_at_omitted_value {U : Set ℂ} (op : IsOpen U) (simply : IsSimplyConnected U)
    {p a : ℂ} (hp : p∈U) (ha : a∈complexUnitDisk) {f : ℂ → ℂ}
    (hf : NormalizedDiskCoordinate U p f) (skip : a∉f '' U) :
    ∃ g : ℂ → ℂ, NormalizedDiskCoordinate U p g ∧ ‖deriv f p‖<‖deriv g p‖ := by
  let h := diskMobius a ∘ f
  have hol : AnalyticOnNhd ℂ h U := fun z hz => (diskMobius_analyticAt ha (hf.maps hz)).comp (hf.analytic z hz)
  have no (z : ℂ) (hz : z∈U) : h z≠0 := by
    change (f z-a)/(1-conj a*f z)≠0
    exact div_ne_zero (sub_ne_zero.mpr (fun e => skip ⟨z,hz,e⟩)) (diskMobius_den_ne ha (hf.maps hz))
  obtain ⟨q,cq,square⟩ := exists_continuousOn_pow_eq simply op hol.continuousOn
    (show 0∉h '' U from fun ⟨z,hz,eq⟩ => no z hz eq) (two_ne_zero : (2:ℕ)≠0)
  have aq := analytic_continuous_square_root op cq hol (fun z _ => square z) no
  have mapq (z : ℂ) (hz : z∈U) : q z∈complexUnitDisk := by
    have sz : ‖q z‖^2<1 := by rw [← norm_pow,square]; exact mem_ball_zero_iff.mp (diskMobius_mapsTo ha (hf.maps hz))
    apply mem_ball_zero_iff.mpr
    nlinarith [norm_nonneg (q z)]
  let b := q p
  have hb : b∈complexUnitDisk := mapq p hp
  let g := diskMobius b ∘ q
  let B := fun w => diskMobius (-a) ((diskMobius (-b) w)^2)
  have sqMap {z : ℂ} (hz : z∈complexUnitDisk) : z^2∈complexUnitDisk := by
    rw [mem_ball_zero_iff,norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.mp hz) two_ne_zero
  have mb : MapsTo B complexUnitDisk complexUnitDisk := fun w hw => diskMobius_mapsTo (diskMobius_neg_mem ha)
    (sqMap (diskMobius_mapsTo (diskMobius_neg_mem hb) hw))
  have ab : AnalyticOnNhd ℂ B complexUnitDisk := by
    intro w hw
    let W := fun t : ℂ => (diskMobius (-b) t)^2
    have aw : AnalyticAt ℂ W w := (diskMobius_analyticAt (diskMobius_neg_mem hb) hw).pow 2
    have outer : AnalyticAt ℂ (diskMobius (-a)) (W w) :=
      diskMobius_analyticAt (diskMobius_neg_mem ha) (sqMap (diskMobius_mapsTo (diskMobius_neg_mem hb) hw))
    exact outer.comp (f:=W) (x:=w) aw
  have mg : MapsTo g U complexUnitDisk := fun _ hz => diskMobius_mapsTo hb (mapq _ hz)
  have ag : AnalyticOnNhd ℂ g U := fun z hz => (diskMobius_analyticAt hb (mapq z hz)).comp (aq z hz)
  have back (z : ℂ) (hz : z∈U) : B (g z)=f z := by
    dsimp only [B,g,Function.comp_apply]
    rw [diskMobius_inverse hb (mapq z hz),square]
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
#print axioms TwoAxisHelicoid.disk_coordinate_improves_at_omitted_value
