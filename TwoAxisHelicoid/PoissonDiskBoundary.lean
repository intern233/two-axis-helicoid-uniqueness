import TwoAxisHelicoid.PoissonDiskInterior

namespace TwoAxisHelicoid
open Complex Set Metric Filter Topology Function InnerProductSpace Real
open scoped Topology

theorem continuousOn_disk_poisson_kernel {c w : ℂ} {r : ℝ} (hw : w∈ball c r) :
    ContinuousOn (poissonKernel c w) (sphere c r) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  apply Complex.continuous_re.comp_continuousOn
  have no : w∉sphere c |r| := by
    rw [abs_of_pos (pos_of_mem_ball hw)]
    exact fun hs => (mem_ball.mp hw).ne (mem_sphere.mp hs)
  simpa only [abs_of_pos (pos_of_mem_ball hw)] using continuousOn_herglotzRieszKernel_sphere no

/-- At every boundary point of a disk the Poisson integral tends to
the specified continuous boundary value. The kernel mass far from the
boundary point tends uniformly to zero. -/
theorem disk_poisson_tendsto_boundary {c p : ℂ} {r : ℝ} (rp : 0<r) {b : ℂ → ℝ}
    (cont : ContinuousOn b (sphere c r)) (hp : p∈sphere c r) :
    Tendsto (diskPoissonValue b c r) (𝓝[ball c r] p) (𝓝 (b p)) := by
  have cb : ContinuousOn (fun z => b z-b p) (sphere c r) := cont.sub continuousOn_const
  have bound := ((isCompact_sphere c r).image_of_continuousOn cb).isBounded
  obtain ⟨B,allB⟩ := bound.exists_norm_le
  have gb (z : ℂ) (hz : z∈sphere c r) : |b z-b p|≤B :=
    allB _ (mem_image_of_mem (fun z => b z-b p) hz)
  have bn : 0≤B := (abs_nonneg _).trans (gb p hp)
  have hpNorm : ‖p-c‖=r := by simpa only [← dist_eq_norm] using mem_sphere.mp hp
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  let a := ε/3
  have ap : 0<a := by dsimp [a]; positivity
  obtain ⟨d,dp,δ⟩ := Metric.continuousWithinAt_iff.mp (cont p hp) a ap
  have close : ∀ᶠ w in 𝓝 p, (r^2-‖w-c‖^2)*B<a*(d/2)^2 := by
    have h : Continuous (fun w : ℂ => (r^2-‖w-c‖^2)*B) := by fun_prop
    apply h.continuousAt.eventually_lt continuousAt_const
    rw [hpNorm,sub_self,zero_mul]
    positivity
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p (half_pos dp)),
    close.filter_mono nhdsWithin_le_nhds] with w hw wp small
  let P := poissonKernel c w
  have cp := continuousOn_disk_poisson_kernel hw
  have Ppos (z : ℂ) (hz : z∈sphere c r) := disk_poisson_kernel_nonnegative hw hz
  let G := fun z => P z*(b z-b p)
  have cg : ContinuousOn G (sphere c r) := cp.mul (cont.sub continuousOn_const)
  have mass : Real.circleAverage P c r=1 := disk_poisson_kernel_mass hw
  have eq : diskPoissonValue b c r w-b p=Real.circleAverage G c r := by
    have funEq : G=(fun z => P z*b z-b p • P z) := by funext z; simp [G,smul_eq_mul]; ring
    have int₁ : CircleIntegrable (fun z => P z*b z) c r := (cp.mul cont).circleIntegrable rp.le
    have int₂ : CircleIntegrable (fun z => b p • P z) c r := (cp.const_smul (b p)).circleIntegrable rp.le
    rw [funEq,Real.circleAverage_fun_sub int₁ int₂,Real.circleAverage_fun_smul,mass,smul_eq_mul,mul_one]
    rfl
  have pt (z : ℂ) (hz : z∈sphere c r) : |G z|≤a • P z+a := by
    change |P z*(b z-b p)|≤a*P z+a
    rw [abs_mul,abs_of_nonneg (Ppos z hz)]
    by_cases near : dist z p<d
    · have less : |b z-b p|<a := by simpa [Real.dist_eq] using δ hz near
      nlinarith [mul_le_mul_of_nonneg_left less.le (Ppos z hz)]
    · have far : d/2≤‖z-w‖ := by
        have tri := dist_triangle z w p
        rw [dist_eq_norm z w] at tri
        linarith [mem_ball.mp wp,le_of_not_gt near]
      have fpos : 0<‖z-w‖ := (half_pos dp).trans_le far
      have len : ‖z-c‖=r := by simpa only [← dist_eq_norm] using mem_sphere.mp hz
      have large : P z*|b z-b p|≤a := by
        apply (mul_le_mul_of_nonneg_left (gb z hz) (Ppos z hz)).trans
        change ((‖z-c‖^2-‖w-c‖^2)/‖z-c-(w-c)‖^2)*B≤a
        rw [len,show z-c-(w-c)=z-w by ring,div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos fpos)]
        exact small.le.trans (mul_le_mul_of_nonneg_left (sq_le_sq₀ (half_pos dp).le fpos.le |>.2 far) ap.le)
      linarith [mul_nonneg ap.le (Ppos z hz)]
  have loInt : CircleIntegrable (fun z => |G z|) c r := cg.abs.circleIntegrable rp.le
  have hiInt : CircleIntegrable (fun z => a • P z+a) c r := ((cp.const_smul a).add continuousOn_const).circleIntegrable rp.le
  have comp := Real.circleAverage_mono loInt hiInt (fun z hz => pt z (by rwa [abs_of_pos rp] at hz))
  have avg : Real.circleAverage (fun z => a • P z+a) c r=a+a := by
    have integr : CircleIntegrable (fun z => a • P z) c r := (cp.const_smul a).circleIntegrable rp.le
    rw [Real.circleAverage_fun_add integr (circleIntegrable_const a _ _),
      Real.circleAverage_fun_smul,Real.circleAverage_const,mass,smul_eq_mul,mul_one]
  rw [Real.dist_eq,eq]
  have lim := (Real.abs_circleAverage_le_circleAverage_abs (f:=G) (c:=c) (R:=r)).trans (comp.trans_eq avg)
  dsimp [a] at lim
  linarith

/-- Dirichlet existence on an actual closed coordinate disk. -/
theorem continuous_disk_dirichlet_solution {c : ℂ} {r : ℝ} (rp : 0<r) {b : ℂ → ℝ}
    (cont : ContinuousOn b (sphere c r)) :
    ∃ u : ℂ → ℝ, HarmonicOnNhd u (ball c r) ∧ ContinuousOn u (closedBall c r) ∧ EqOn u b (sphere c r) := by
  classical
  let u := (ball c r).piecewise (diskPoissonValue b c r) b
  have agree (p : ℂ) (hp : p∈sphere c r) : u p=b p := piecewise_eq_of_notMem _ _ _ (fun h => (mem_ball.mp h).ne (mem_sphere.mp hp))
  have inside (p : ℂ) (hp : p∈ball c r) : u =ᶠ[𝓝 p] diskPoissonValue b c r := by
    filter_upwards [isOpen_ball.mem_nhds hp] with z hz using piecewise_eq_of_mem _ _ _ hz
  have harm : HarmonicOnNhd u (ball c r) := fun p hp => (harmonicAt_congr_nhds (inside p hp)).mpr (disk_poisson_value_harmonic rp cont p hp)
  refine ⟨u,harm,?_,agree⟩
  intro p hp
  rcases (mem_closedBall.mp hp).lt_or_eq with inner|bd
  · exact (harm _ inner).1.continuousAt.continuousWithinAt
  · have hs : p∈sphere c r := bd
    have h1 : ContinuousWithinAt u (ball c r) p := by
      change Tendsto u _ (𝓝 (u p))
      rw [agree p hs]
      exact (disk_poisson_tendsto_boundary rp cont hs).congr' (by
        filter_upwards [self_mem_nhdsWithin] with _ h using (piecewise_eq_of_mem _ _ _ h).symm)
    have h2 : ContinuousWithinAt u (sphere c r) p := (cont p hs).congr (fun z hz => agree z hz) (agree p hs)
    exact (h1.union h2).mono (fun z hz => (mem_closedBall.mp hz).lt_or_eq)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.continuous_disk_dirichlet_solution
