namespace t
class Functor (f : Type u → Type u) where
  map :  ∀ {α β : Type u}, (α → β) → f α → f β

-- Example instance for Option
instance : Functor Option where
  map f o :=
    match o with
    | none   => none
    | some x => some (f x)
end t
