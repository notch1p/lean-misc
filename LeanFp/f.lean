instance : Applicative List where
  pure := List.pure
  seq f x := List.bind f (λ y => Functor.map y (x ()))

#eval (· + · + ·) <$> [1, 2] <*> [3, 4] <*> [5, 6]


instance : Monad List where
  pure := List.pure
  bind := List.bind

#check List.pure -- α -> List α
#check List.bind -- List α -> (α -> List β) -> List β
-- adjoint
