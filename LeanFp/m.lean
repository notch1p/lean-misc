instance : Monad Option where
  pure := .some
  bind := .bind


#eval (pure 10 : Option Nat) >>= fun x => pure (x + 1)
