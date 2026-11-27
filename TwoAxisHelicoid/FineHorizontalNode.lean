import TwoAxisHelicoid.PreciseHorizontalTheta

namespace TwoAxisHelicoid
open Complex

structure FineHorizontalNode where
  point : DyadicBall
  function : DyadicThetaATrace

def FineHorizontalNode.Valid (w : FineHorizontalNode) (p : RootDyadicParameters) (t x : ℚ) : Prop :=
  (w.point.toBall 128).coarsens (ComplexBall.point ⟨x,t/2⟩) ∧
    w.function.FineValid horizontalFineConfig horizontalFinePi 8 (2^48)
      p.q.output p.abscissa p.coefficient.output w.point

instance FineHorizontalNode.instDecidableValid (w : FineHorizontalNode) (p : RootDyadicParameters) (t x : ℚ) : Decidable (w.Valid p t x) := by
  unfold FineHorizontalNode.Valid
  infer_instance

def FineHorizontalNode.lower (w : FineHorizontalNode) : ℚ :=
  (w.function.output.toBall 128).center.re-(w.function.output.toBall 128).radius
def FineHorizontalNode.upper (w : FineHorizontalNode) : ℚ :=
  (w.function.output.toBall 128).center.re+(w.function.output.toBall 128).radius

theorem FineHorizontalNode.sound {w : FineHorizontalNode} {p : RootDyadicParameters} {t x l u : ℚ}
    (data : p.HorizontalFineValid t t l u) (ok : w.Valid p t x)
    {a : ℝ} (al : (l:ℝ)≤a) (au : a≤(u:ℝ)) :
    (w.lower:ℝ)≤(thetaA (t:ℝ) a ((x:ℂ)+I*((t:ℝ)/2:ℝ))).re ∧
      (thetaA (t:ℝ) a ((x:ℂ)+I*((t:ℝ)/2:ℝ))).re≤(w.upper:ℝ) := by
  obtain ⟨ht,q,ab,co⟩ := p.horizontalFine_sound data le_rfl le_rfl al au
  have point := ComplexBall.coarsen_contains (ComplexBall.point_contains (⟨x,t/2⟩:QComplex)) ok.1
  have val : (⟨x,t/2⟩:QComplex).val=(x:ℂ)+I*((t:ℝ)/2:ℝ) := by
    apply Complex.ext <;> simp [QComplex.val,Complex.mul_re,Complex.mul_im]
  rw [val] at point
  have out := (w.function.fine_sound horizontalFineConfig horizontalFinePi_contains 8 (2^48) q ab co point
    (horizontalFine_tail ht 0 (by norm_num)) (horizontalFine_tail ht 1 le_rfl) ok.2).1
  simpa only [FineHorizontalNode.lower,FineHorizontalNode.upper,horizontalFineConfig,Rat.cast_add,Rat.cast_sub] using ComplexBall.re_bounds out

def fineHorizontalNodeRun (p : RootDyadicParameters) (t : ℚ) (N : ℕ) : ℕ → List FineHorizontalNode → Prop
  | _,[] => True
  | k,w::ws => w.Valid p t (-1+(k:ℚ)/N) ∧ fineHorizontalNodeRun p t N (k+1) ws

theorem fineHorizontalNodeRun_append {p : RootDyadicParameters} {t : ℚ} {N k : ℕ} {a b : List FineHorizontalNode}
    (left : fineHorizontalNodeRun p t N k a) (right : fineHorizontalNodeRun p t N (k+a.length) b) :
    fineHorizontalNodeRun p t N k (a++b) := by
  induction a generalizing k with
  | nil => simpa only [List.nil_append,List.length_nil,Nat.add_zero] using right
  | cons w a ih =>
    refine ⟨left.1,ih left.2 ?_⟩
    simpa only [List.length_cons,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using right

theorem fineHorizontalNodeRun_get {p : RootDyadicParameters} {t : ℚ} {N k : ℕ} {ws : List FineHorizontalNode}
    (ok : fineHorizontalNodeRun p t N k ws) (i : Fin ws.length) :
    (ws.get i).Valid p t (-1+((k+i.val:ℕ):ℚ)/N) := by
  induction ws generalizing k with
  | nil => exact Fin.elim0 i
  | cons w ws ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.val_zero,Nat.add_zero,List.get_cons_zero] using ok.1
    · have tail := ih ok.2 j
      simpa only [Fin.val_succ,List.get_cons_succ',Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using tail

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.FineHorizontalNode.sound
#print axioms TwoAxisHelicoid.fineHorizontalNodeRun_get
