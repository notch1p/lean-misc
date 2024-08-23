import «LeanFp»


def main : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting


-- def thirtyNine : ℕ := 39

abbrev ℕ := Nat

structure Point where
  x: Float
  y: Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }
#eval origin

structure RectangularPrism where
  height: Float
  width: Float
  depth: Float
deriving Repr

def volume (prism: RectangularPrism): Float :=
  1.0/3 * prism.depth * prism.width * prism.height

inductive Boolean where
  | false: Boolean
  | true: Boolean


-- def fib (n: Nat) :=
--   match n with
--   | 0 => 0
--   | 1 => 1
--   | n + 2 => fib (n + 1) + fib n

def fib(n: ℕ) :=
  match n with
  | 0 => 0
  | 1 => 1
  | k + 2 => fib (k + 1) + fib (k)

#eval fib 10


def sigma (l : Nat) (r : Nat) (f : Nat -> Nat): Nat :=
  List.range (r - l + 1)
  |> .map (λ n => f (l + n))
  |> List.foldl (· + ·) 0

#eval sigma 1 10 id -- => 55

#check [1,2,3]

def evenp (n: Nat) := n &&& 1 == 0

def length (α: Type) (l: List α) :=
  match l with
  | [] => 0
  | _ :: xs => 1 + length α xs

inductive MyType (α : Type) : Type where
  | ctor : α → MyType α

def last {α: Type} (l: List α): Option α :=
  match l with
  | [] => none
  | x :: [] => x
  | _ :: xs => last xs

def findFirst? {α: Type} (xs: List α) (predicate: α -> Bool) (index: Option Nat := some 0): Option Nat :=
  match xs with
  | [] => none
  | x :: l =>
    match index with
    | none => none
    | some n => if predicate x then n else findFirst? l predicate (some (n + 1))

#eval findFirst? [1,2,3,3,4,4,5] (λ x => x == 3)



def Prod.swap {α β: Type} (pair: α × β): β × α := (pair.2, pair.1)


def zip {α β: Type} (xs: List α) (ys: List β): List (α × β) :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xl, y :: yl => (x,y) :: zip xl yl

def take {α: Type} (n: Nat) (l: List α): List α :=
  match n,l with
  | 0, _ => []
  | _, [] => []
  | n + 1, x :: ls => x :: take n ls

#eval take 3 [1,2,3,4,5]

def distribute {α β γ : Type} : α × (β ⊕ γ) -> (α × β) ⊕ (α × γ)
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)

def mul_by_plus2 {α: Type}: Bool × α -> α ⊕ α
  | (_, a) => Sum.inl a

#check Sum.inl (Sum Nat String)

-- open Nat

-- def gcd (a b: ℕ): ℕ :=
--   match b with
--   | 0 => a
--   | b + 1 => gcd (b + 1) (a % (b + 1))
--   termination_by b
--   decreasing_by
--     simp_wf;
--     apply mod_lt _ (zero_lt_of_ne_zero _);
--     apply add_one_ne_zero

unsafe def gcd_unsafe: ℕ -> ℕ -> ℕ
  | a, 0 => a
  | a, b + 1 => gcd_unsafe (b + 1) (a % (b + 1))


#check (· ∧ ·)
#check (· == ·)



def fact: ℕ -> ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def ackermann: ℕ -> ℕ -> ℕ
  | 0, n => n + 1
  | m + 1, 0 => ackermann m 1
  | m + 1, n + 1 => ackermann m (ackermann (m + 1) n)


unsafe inductive μ (α : Type u) : Type u
  | fold : (μ α -> α) -> μ α

unsafe def unfold : μ α -> (μ α -> α)
  | .fold f => f

unsafe def M (x : μ α) : α := unfold x x

unsafe def fix (t : (α -> α) -> α -> α) : α -> α :=
  let Wt : μ (α -> α) := .fold (λ f => t (unfold f f))
  M Wt

-- unsafe def fix (f : (α -> α) -> α -> α) : α -> α :=
--   let M: μ (α -> α) := μ.fold (λ x => (unfold x x))
--   let W := μ.fold (λ x => (λ y => x unfold (y y)))
--   -- M W

unsafe def gen_factorial (f : ℕ -> ℕ) (n : ℕ) : ℕ :=
  if n = 0 then 1 else n * f (n - 1)

#eval fix gen_factorial 25

unsafe def fix_rec (f : (α -> α) -> α -> α) (x) := f (fix_rec f) x


inductive BinaryTree (α : Type) : Type where
  | Leaf : BinaryTree α
  | Node : α -> BinaryTree α -> BinaryTree α -> BinaryTree α
