instance : Applicative List where
  pure := List.pure
  seq f x := List.bind f (λ y => Functor.map y (x ()))

#eval (· + · + ·) <$> [1, 2] <*> [3, 4] <*> [5, 6]


instance : Monad List where
  pure := List.pure
  bind := List.bind

@[inline] def Array.pure (x : α) : Array α := #[x]

-- instance : Monad Array where
--   pure := Array.pure
--   bind xs f := .concatMap f xs

#check List.pure -- α -> List α
#check List.bind -- List α -> (α -> List β) -> List β
-- adjoint


inductive Maybe (α : Type) where
  | none : Maybe α
  | some : α -> Maybe α

instance : Applicative Maybe where
  pure := .some
  seq f x := match f with
    | .none => .none
    | .some f => match x () with
      | .none => .none
      | .some x => .some (f x)


#check pure 10 (α := Nat) (f := Option)

#check pure (· + ·) <*> some 10 <*> some 5

#check (· + ·) <$> some 10 <*> some 5

def cartesian [Applicative F] : F α -> F β -> F (α × β)
  | xs, ys => Prod.mk <$> xs <*> ys

#check Prod.mk (α := Nat) (β := Nat) <$> [1,2,3]

#eval [1,2,3].map λ x => [4,5,6].map (λ y => (x, y))

class Mappable (C : Type u -> Type v) where -- Monadic
  map  : (α -> β) -> C α -> C β
  bind : C α -> (α -> C β) -> C β

#check @Mappable

#check bind
instance : Mappable List where
  map  := .map
  bind := .bind

instance : Mappable Array where
  map       := .map
  bind xs f := .concatMap f xs

#check Applicative List

open Mappable(map bind) in
def cartesianM [Mappable L] (xs : L α) (ys : L β) : L (α × β) :=
  bind xs (λ x => map (λ y => (x, y)) ys)

#eval cartesianM #[1,2,3] #[4,5,6,7] |>.foldl (λ (x : Array Nat) y => x ++ #[y.1,y.2]) #[]

def cartesian_imperative (xs : List Nat) (ys : List Nat) : List (Nat × Nat) := do
  let mut zs := []
  for x in xs do
    for y in ys do
      zs := zs ++ [(x, y)]
  zs

#eval cartesian_imperative [1,2,3] [4,5,6,7]

def sideEffect (xs : List Nat) : List Nat :=
  do
    let y := (<- xs) + 1
    return y

#eval (· + ·) <$> [1,2,3] <*> [4,5,6]


def printList (xs : List Nat) : IO Unit :=
  xs.forM (fun x => IO.println x)
