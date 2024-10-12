structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := {num := n, den := 1, inv := by decide}

instance : ToString Rational where
  toString r := if r.den == 1 then toString r.num else s!"{r.num}/{r.den}"

#eval (2 : Rational)

#eval nat_lit 2


abbrev ℕ := Nat

instance : HMul ℕ (List ℕ) (List ℕ) where
  hMul x ys := ys.map (· * x)

open HMul(hMul)

#eval hMul 2 [1,2,3,4]

open Nat(mul_ne_zero) in
def Rational.add (x y : Rational) : Rational :=
  ⟨yden * x.num + xden * y.num, x.den * y.den, inv⟩ where
  inv := mul_ne_zero x.inv y.inv
  yden : Int := y.den
  xden : Int := x.den
