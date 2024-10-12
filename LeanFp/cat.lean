#check Empty

def factorizer : (γ -> α) -> (γ -> β) -> (γ -> α × β)
  | p, q => λ x => (p x, q x)

def factorizer_sum : (α -> γ) -> (β -> γ) -> α ⊕ β -> γ
  | i, _, .inl a => i a
  | _, j, .inr b => j b

section
/-- An F-Algebra `⟨f, a, f a → a⟩` where
  - `f`: An endofunctor
  - `a`: An object (i.e. type as in 𝐓𝐲𝐩𝐞)

```plaintext
*----------------------------------------*
| F a ---- `in` ----> a           𝐂      |
|  |                  |                  |
| F h                `h`                 |
|  ↓                  ↓                  |
| F x ---- `f`  ----> x                  |
*----------------------------------------*
```
Here `⟨a, in⟩` is a initial F-algebra for some endofunctor `F`;
`⟨x, f⟩` is a another one f-algebra. By the definition of _initial_ there exists
a unique homomorphism `h : ⟨a, in⟩ → ⟨x, f⟩`.

**Lambek's theorem**
for some endofunctor `F`,
∃A : F α -> α, A is initial => α is _isomorphic_ to F α via A.

where `h = cata f` and by Lambek (F a ~= a) we have `out : a → F a`, thus
```lean4
let rec cata f := f ∘ F (cata f) ∘ out
```
also  `h ∘ in = f ∘ F h`; `in = Fix`; `out = unfix`.
-/
abbrev Algebra (f : Type -> Type) α := f α -> α

inductive Ring (α : Type) where
  | Zero
  | One
  | Add : α -> α -> Ring α
  | Neg : α -> Ring α

abbrev Ring₁ α := Ring (Ring α)
abbrev Ring₂ α := Ring (Ring (Ring α))

/--
self-application.
- Ring_{n+1} α = Ring $ Ring_n α i.e. replace (α : Binder) w/ Ring.
- Ringₙ = Expr. (n → ∞) eventually there will be no α.
-/
inductive Expr where
  | EZero
  | EOne
  | EAdd : Expr -> Expr -> Expr
  | ENeg : Expr -> Expr

/-- (Ring, Int, eval) forms a F-Algebra. -/
def eval : Algebra Ring Int
  | .Zero    => 0
  | .One     => 1
  | .Add m n => m + n
  | .Neg n   => - n
#reduce (types := true) Algebra Ring Int

def evalE : Expr -> Int
  | .EZero      => 0
  | .EOne       => 1
  | .EAdd e₁ e₂ => evalE e₁ + evalE e₂
  | .ENeg e     => - evalE e
end

def ini : Option Nat -> Nat
  | .none =>  0
  | .some n => n + 1

instance : Functor Option where
  map f s :=
    match s with
    | .none => .none
    | .some n => .some <| f n

example (hp : p) (hnp : ¬p) : q := absurd hp hnp

/--
An endo (within the **Type** category)-bifunctor 𝐂 × 𝐃 → 𝐄:

```
  a ----------> c    -- 𝐂-------------- |
  ↓----`fst`----↓                       |
F a b ------> F c d  -- 𝐄 <---`bimap`---|
    ↑----`snd`----↑                     |
    b ----------> d  -- 𝐃---------------|
```
-/
class Bifunctor (F : Type -> Type -> Type) where
  bimap  : (α -> γ) -> (β -> δ) -> F α β -> F γ δ
  first  : (α -> γ) -> F α β -> F γ β := λ g => bimap g id
  second : (β -> δ) -> F α β -> F α δ := bimap id

instance : Bifunctor Prod where
  bimap f g | (x, y) => (f x, g y)

instance : Bifunctor Sum where
  bimap f g
  | .inl x => .inl $ f x
  | .inr y => .inr $ g y

#eval Bifunctor.bimap (· + 2) id (.inl 1 : _ ⊕ String)
#eval Bifunctor.bimap (· + 2) (· - 4) (2,3)

structure BiComp
  (bf : Type -> Type -> Type)
  (fu gu : Type -> Type)
  (a b : Type)
where
  val : (bf (fu a) (gu b))

open Bifunctor in
open Functor(map) in
instance
  [Bifunctor bf]
  [Functor fu]
  [Functor gu] : Bifunctor $ BiComp bf fu gu
where
  bimap f₁ f₂
  | {val} => ⟨(bimap (map f₁) (map f₂)) <| val⟩

#check Functor.map (f := List) (· + 2)

abbrev Reader : Type -> Type -> Type -- A function-type constructor.
  | r, a => r -> a

instance : Functor $ Reader r where
  -- it's also a functor.
  -- maps a -> b to be R (ra) -> R(rb) i.e. (r -> a) -> (r -> b)
  -- (r -> a) |> (a -> b) => r -> b
  -- i.e. insert a morph `f` after `g`
  map f g := f ∘ g

abbrev Op (r a : Type) := a -> r -- A function-typeᵒᵖ constructor.

/--
the fancy word _Contravariant_ means the 2 **horizontal** arrows in the below
commute graph face opposite direction:
- (Co) here means a covariant functor.
- Typesᵒᵖ has a regular functor Coᵒᵖ

```
Co r α ---`Co fᵒᵖ`---> Co r β
   ↑--------`cmap`--------↑
   α <--------`f`-------- β
```
-/
class Contravariant (F : Type -> Type) where
  cmap : (β -> α) -> F α -> F β
--     : (β -> α) -> (α -> r) -> β -> r

instance : Contravariant (Op r) where
  -- it's also a functor.
  -- maps b -> a to be Opᵣ(a) -> Opᵣ(b)
  -- i.e. (a -> r) -> (b -> r)
  -- i.e. (b -> a) |> a -> r => b -> r
  -- i.e. insert `f` before `g`.
  cmap f g := g ∘ f
--  alternatively,
--  cmap f g := flip (· ∘ ·) f g

section open Contravariant(cmap)
variable (α β r : Type)
#check flip (· ∘ ·) (β := β -> α) (α := α -> r)
#check cmap (F := Op Nat) (λ _ : String => true)
#reduce @cmap (Op Nat) _ _ _ (λ _ : String => true) (λ _ : Bool => 1)
end


/--
A profunctor of 𝐂ᵒᵖ × 𝐃 -> 𝐒𝐞𝐭:

```
  β <---`f`---- α   -- 𝐂ᵒᵖ--------
  ↓---`lmap`----↓                |
P β γ--Pfg--->P α δ -- 𝐒𝐞𝐭 <--`dimap`
    ↑---`rmap`----↑              |
    γ ---`g`----> δ -- 𝐃----------
```

A Hom-functor is a profunctor where 𝐃 = 𝐂.
-/
class Profunctor (p : Type -> Type -> Type) where
  dimap (f : α -> β)
        (g : γ -> δ)
      : p β γ -> p α δ

  lmap  (f : α -> β) : p β γ -> p α γ
    := dimap f id

  rmap  (g : γ -> δ) : p β γ -> p β δ
    := dimap id g

/--
a^(b + c) = a^b × a^c.
Here `=` means isomorphic.
-/
def expo_sum : Sum Int Float -> String
/- a pair of functions -/
  | .inl x => s!"of {x}:Int"    -- Int -> String
  | .inr y => s!"of {y}:Float"  -- Float -> String

/-
(a^b)^c = a^(b × c). basically currying.
-/

def eval_cat {α β : Type} : (α -> β) × α -> β | (f, x) => f x

def mp (p q : Prop) : Prop := p -> q


/--
For rectype see `«LeanFp.Basic».μtype`.
Also see
[fixpoint-comb](https://www.notch1p.xyz/fixpoint-comb)
[nlab](https://ncatlab.org/nlab/show/catamorphism).

`F i ~= i`. there exists a isomorphism j between initial object i and F i.
which looks like f x = x. Another way to interpret this is to treat `i` as a
fixpoint of F. Thus with fixcomb we have `Fix = j`; `Fix F = i`. Trivially
- `F (Fix F) = Fix F`. In terms of functor `F`, we replace its argument (type) with
`Fix F` such that to the point where `Fix F` does not depend on that type anymore.

 F (Fix F) ----- F m -----> F a
   ↑unfix                   |alg
Fix↓                        ↓
 Fix F --------- m -------> a

- `Fix F` is initial. Thus there exists a unique morph `m` from Fix F to some other
algebra `a`. `m` may also be seen as an `eval` which reduce the rectree.

obviously we have
- `m = alg ∘ F m ∘ unfix` (terminates as long as `F m` being a finite rectree. Lean wouldn't be able to tell that though.)
- `map m = F m` (lifting m)

In programming, we may say only initial F-algebra matters.
-/
unsafe inductive Fix (f : Type -> Type)
  | fix : f (Fix f) -> Fix f

unsafe def unfix : Fix f -> f (Fix f)
  | .fix f => f

open Functor(map) in
unsafe def cata [Functor F] : (F α -> α) -> Fix F -> α
  | alg => alg ∘ map (cata alg) ∘ unfix

/--
An endofunctor of NatF A = 1 + A.

Nat = Fix NatF.
Nat does not depend on A. Intuitively, To tranform an NatF to Nat, we _fix_ NatF.
Through this Nat together with \[zero,succ\] becomes an initial object.
-/
inductive NatF (A : Type u)
  | ZeroF
  | SuccF : A -> NatF A
deriving Repr

instance : Functor NatF where
  map f
  | .ZeroF => .ZeroF
  | .SuccF a => .SuccF $ f a

def fib : NatF (Int × Int) -> Int × Int -- An algebra
  | .ZeroF => (1, 1)
  | .SuccF (m, n) => (n, m + n)

#check cata fib

inductive ListF (e : Type) (α : Type) where
  | nilF
  | consF : e -> α -> ListF e α
deriving Repr

def lenAlg : ListF e Int -> Int -- An algebra
  | .nilF => 0 --------------------------*
  | .consF _ n => n + 1--------*         |
--                             ↓         ↓
#eval [1,2,3,4].foldr (λ _ a => a + 1) 0

instance : Functor (ListF e) where
  map f
  | .nilF => .nilF
  | .consF e a => .consF e (f a)

section open NatF Fix ListF
#eval cata fib <| fix $ SuccF $ fix $ SuccF $ fix $ SuccF $ fix ZeroF
#check fix $ SuccF $ fix $ ZeroF
#check fix ZeroF -- the solution to NatF A ~= A i.e. fix ZeroF === Nat.zero
/-
`f` is unified by the typechecker to be NatF
`NatF A` is unified by `f (Fix f)` which in this case is `NatF (Fix NatF)`
thus A is `Fix NatF`
-/
#eval cata lenAlg <| fix $ consF 4 $
                     fix $ consF 3 $
                     fix $ consF 2 $
                     fix $ consF 1 $
                     fix nilF
/- equivalent of -/ #eval [1,2,3,4].foldr (λ _ x => x + 1) 0
end

#check Nat -- (Nat, [.zero, .succ]) is a initial F-algebra.

#check @Nat.zero
