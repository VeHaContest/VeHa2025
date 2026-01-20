import Auto
import Lean

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open TotalCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.timeout 2
set_option auto.smt.solver.name "z3"

--this will ne our answer type
structure SubstringResult where
  l : Nat
  r : Nat
  flag: Bool
deriving Repr

--predicate for substring all characters of which satisfy the predicate
@[reducible]
def CorrectSubstring (s : Array Char) (p : Char -> Bool) (l r : Nat) : Prop :=
  l ≤ r ∧ r < s.size ∧
  (∀ i, l ≤ i ∧ i ≤ r → p s[i]!)

--actual method
--  if there are no substrings,
--  flag is false and all characters do not satisfy the predicate
method SubstringSearch (s: Array Char) (p: Char -> Bool) return (res: SubstringResult)
--postconditions, don't need any preconditions.
ensures (res.l ≤ res.r)
ensures 0 < s.size → res.r < s.size
ensures res.flag → CorrectSubstring s p res.l res.r
ensures res.flag →
  (∀ l₁ r₁, CorrectSubstring s p l₁ r₁ →
    r₁ - l₁ + 1 = res.r - res.l + 1 ∧ res.r ≤ r₁ ∨
    r₁ - l₁ + 1 < res.r - res.l + 1)
ensures ¬res.flag → ∀ i < s.size, ¬p s[i]!
do
    if s.size = 0 then
      --basic case with an empty string
      return ⟨0, 0, false⟩
    let mut cnt := 0
    let mut pnt := 0
    let mut ans := 0
    let mut l_ans := 0
    let mut r_ans := 0
    while pnt < s.size
    --loop invariants
    invariant 0 ≤ cnt
    invariant cnt ≤ pnt
    invariant pnt ≤ s.size
    invariant l_ans ≤ r_ans
    invariant r_ans < s.size
    invariant cnt ≤ ans
    invariant r_ans ≤ pnt
    invariant ∀ j, pnt - cnt ≤ j ∧ j < pnt → p s[j]!
    invariant ans > 0 →
        ans = r_ans - l_ans + 1 ∧
        CorrectSubstring s p l_ans r_ans
    invariant ans = 0 → (∀ i, i < pnt → ¬p s[i]!)
    invariant cnt < pnt → ¬p s[pnt - cnt - 1]!
    invariant ∀ l₁ r₁,
        CorrectSubstring s p l₁ r₁ ∧ r₁ < pnt →
        r₁ - l₁ + 1 = ans ∧ r_ans ≤ r₁ ∨ r₁ - l₁ + 1 < ans
    --value decreases by 1 with each iteration,
    --therefore time complexity is O(size s), as other parts
    --take constant time
    decreasing s.size - pnt
    do
      --loop body
      if p s[pnt]! then
        cnt := cnt + 1
        if ans < cnt then
          l_ans := pnt + 1 - cnt
          r_ans := pnt
          ans := cnt
      else
        cnt := 0
      pnt := pnt + 1
    return ⟨l_ans, r_ans, ans > 0⟩

set_option maxHeartbeats 10000000 in
-- goals involve too many universal quantifiers, need more heartbeats
prove_correct SubstringSearch by
  loom_goals_intro
  loom_unfold
  all_goals loom_auto
  { unhygienic intros
    by_cases hi: l₁ = pnt
    { by_cases eq: pnt = cnt <;> loom_auto }
    have lem := invariant_12 l₁ r₁ a (by omega) a_2
    loom_auto }
  { unhygienic intros
    by_cases hi: r₁ = pnt
    { by_cases eq: pnt = cnt <;> loom_auto }
    apply invariant_12
    all_goals loom_auto }
  { unhygienic intros
    by_cases hi: r₁ = pnt
    { loom_auto }
    apply invariant_12
    all_goals loom_auto }
  { exact invariant_12 }
  { unhygienic intros
    have := invariant_12 l₁ r₁ a_1 (by omega) a_3
    loom_auto }

--prove theorem not about the monadic computation but the actual
--run result
theorem finalCorrectnessTheorem (s : Array Char) (p : Char → Bool) :
  (match (SubstringSearch s p).run with
  | .res res =>
    (res.flag = false → ∀ i < s.size, p s[i]! = false) ∧
    (res.flag = true →
     (∀ l₁ r₁, CorrectSubstring s p l₁ r₁ →
    r₁ - l₁ + 1 = res.r - res.l + 1 ∧ res.r ≤ r₁ ∨
    r₁ - l₁ + 1 < res.r - res.l + 1)) ∧
    (res.flag = true → CorrectSubstring s p res.l res.r) ∧
    (0 < s.size → res.r < s.size) ∧
    (res.l ≤ res.r)
  | .div => False) := by
    have lem := ExtractNonDet.extract_refines ⊤ (SubstringSearch s p) (SubstringSearch_correct s p)
    simp [triple, TotalCorrectness.DivM.wp_eq] at lem
    split <;> simp [*] at *
    exact lem

--finds 1234, not 6728
#eval (SubstringSearch "1234ka45l6728y23".toList.toArray Char.isDigit).run
