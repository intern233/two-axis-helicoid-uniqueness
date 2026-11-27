module

public import Init

@[expose] public section
namespace TwoAxisHelicoid.VerticalRunCore

def sumPrefix (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n+1 => sumPrefix f n + f n

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

def piLower : Rat := 314159265358979323846264338327950288419716 / 10^41
def piUpper : Rat := 314159265358979323846264338327950288419717 / 10^41

def expCut (x : Rat) : Rat := sumPrefix (fun k => x^k / (factorial k : Rat)) 44
def expError (x : Rat) : Rat := x.abs^44 / (factorial 44 : Rat) * 2

def expTest (t lo hi : Rat) : Prop :=
  let a := -piUpper*t
  let b := -piLower*t
  a.abs / 45 ≤ 1/2 ∧ b.abs / 45 ≤ 1/2 ∧
  lo ≤ expCut a - expError a ∧ expCut b + expError b ≤ hi

def coefficients : List Nat :=
  [1, 1, 4, 5, 6, 4, 8, 13, 13, 6, 12, 20, 14, 8, 24, 29, 18, 13, 20, 30, 32, 12, 24, 52, 31, 14, 40, 40, 30, 24, 32, 61, 48, 18, 48, 65, 38, 20, 56, 78]

def coefficient (i : Nat) : Nat := (coefficients[i]?).getD 0
def seriesCut (q : Rat) : Rat := sumPrefix (fun i => (coefficient i : Rat) * q^(i+1)) 40
def seriesTail (q : Rat) : Rat :=
  q^41 * (41^2/(1-q) + 2*41*q/(1-q)^2 + q*(1+q)/(1-q)^3)

def seriesTest (lo hi L U : Rat) : Prop :=
  L < 1/4 - 2*(seriesCut hi + seriesTail hi) ∧ 1/4 - 2*seriesCut lo < U

abbrev Tests (t lo hi L U : Rat) : Prop := expTest t lo hi ∧ seriesTest lo hi L U

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem left_display : Tests
    (70945978 / 10^8)
    (10765392093268113736230733970338727 / 10^35) (10765392093268113736230733970338728 / 10^35)
    (-47221253557264140850267997705597 / 10^40) (-47221253557264140850240321370933 / 10^40) := by
  unfold Tests expTest seriesTest
  decide +kernel

theorem right_display : Tests
    (70945980 / 10^8)
    (10765391416858600721767478766631171 / 10^35) (10765391416858600721767478766631172 / 10^35)
    (13998405173549555596490797567326 / 10^39) (13998405173549555596493565200718 / 10^39) := by
  unfold Tests expTest seriesTest
  decide +kernel

theorem left_inner : Tests
    (709459781 / 10^9)
    (10765392059447637076131062167372461 / 10^35) (10765392059447637076131062167372462 / 10^35)
    (-1 / 10^7) 0 := by
  unfold Tests expTest seriesTest
  decide +kernel

theorem right_inner : Tests
    (709459799 / 10^9)
    (10765391450679075363114151510334436 / 10^35) (10765391450679075363114151510334437 / 10^35)
    0 (1 / 10^7) := by
  unfold Tests expTest seriesTest
  decide +kernel

end TwoAxisHelicoid.VerticalRunCore

#print axioms TwoAxisHelicoid.VerticalRunCore.left_display
#print axioms TwoAxisHelicoid.VerticalRunCore.right_display
#print axioms TwoAxisHelicoid.VerticalRunCore.left_inner
#print axioms TwoAxisHelicoid.VerticalRunCore.right_inner
