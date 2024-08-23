import LeanCopilot
class Monoid (α: Type) where
  zero: α
  op: α -> α -> α

def reduce {α: Type} (m: Monoid α) (xs: List α): α :=
  match xs with
  | [] => m.zero
  | [x] => x
  | x::xs => m.op x (reduce m xs)

class ListSlice (α : Type) where
  l: List α
  start: Nat
  finish: Nat

def ListSlice.length (xs : ListSlice α) : Nat :=
  xs.finish + 1 - xs.start

partial def parreduce [Inhabited α] (m : Monoid α) (xs : ListSlice α) : α :=
  match xs.finish + 1 - xs.start with
  | 0 => m.zero
  | 1 => xs.l.get! xs.start
  | 2 => m.op (xs.l.get! xs.start) (xs.l.get! (xs.start + 1))
  | 3 => m.op (m.op (xs.l.get! xs.start) (xs.l.get! (xs.start + 1))) (xs.l.get! (xs.start + 2))
  | n + 4 =>
    let n' := (n + 4) / 2
    let first_half := {xs with finish := xs.start + n' - 1}
    let second_half := {xs with start := xs.start + n'}
    m.op
      (parreduce m first_half)
      (parreduce m second_half)


def whole_slice {α: Type} (l: List α): ListSlice α := ⟨l, 0, l.length - 1⟩

#eval parreduce ⟨0, (· + ·)⟩ (whole_slice [1,2,3,4])

def map_reduce [Inhabited β] (m: Monoid β) (f: α -> β) (xs: List α): β :=
  match xs with
  | [] => m.zero
  | [x] => f x
  | xs => parreduce m (whole_slice (xs.map f))

instance compose_monoid : Monoid (α -> α) :=  ⟨id, λ f g x => f (g x)⟩

#eval ([1,2,3,4].map Int.sub).map (λ x => x 10)

def fold_right (f: α -> β -> β) (init: β) (xs: List α): β :=
  List.map f xs |> reduce compose_monoid <| init

#eval fold_right (α := Int) (β := Int) (· - ·) 10 [1,2,3,4]

#eval [1,2,3,4].foldr (fun x y => x - y) 10

def fold_left (f: α -> β -> α) (init: α) (xs : List β): α :=
  xs.map (fun x => fun init => f init x) |> reduce compose_monoid <| init

#eval fold_left (α := Int) (β := Int) (· - ·) 10 [1,2,3,4]

#eval [1,2,3,4].foldl (· - ·) 10

instance sub_monoid : Monoid (Int × Bool) where
  zero := (0, true)
  op := fun ⟨x₁, b₁⟩ ⟨x₂, b₂⟩ =>
    (if b₁ then x₁ + x₂ else x₁ - x₂, b₁ && b₂)

def fold_right_sub (init: Int) (xs: List Int) : Int :=
  let fst := xs.map (fun x: Int => (x, false)) |> reduce sub_monoid |> Prod.fst
  if xs.length &&& 1 == 0 then init + fst else init - fst

#eval fold_right_sub 10 [1,2,3,4]

def parse_int (s: String): Int :=
  s.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def comp_left (f: α -> β) (g: β -> γ): α -> γ := (λ x => f x |> g)

infixl: 20 " ~> " => comp_left

#eval (· + 1) ~> (· * 2) <| 10

instance horner_monoid: Monoid (Nat × Nat) :=
  ⟨(0,1), λ (x, r₁) (y, r₂) => (x * r₂ + y, r₁ * r₂)⟩

instance : Monoid Nat := ⟨0, (· + ·)⟩

def parse_int_alt : String -> Nat :=
  String.toList
    ~> List.map (λ c => c.toNat - '0'.toNat)
    ~> List.map (λ x => (x, 10)) -- g
    ~> reduce horner_monoid
    ~> Prod.fst -- h

#eval parse_int_alt "2000000"

instance hmonoid [Monoid α] : Monoid (α × (α -> α)) where
  zero := (Monoid.zero, id)
  op := λ ⟨x₁, f₁⟩ ⟨x₂, f₂⟩ => (Monoid.op (f₂ x₁) x₂, f₁ ~> f₂)
