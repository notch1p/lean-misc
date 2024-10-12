def div (x y : Nat) : Except String Nat :=
  if y == 0 then
    throw "Division by zero"
  else
    pure (x / y)

#eval
try
  let res <- div 10 2
  pure (toString res)
catch
  e => pure <| "Error: " ++ e

def divUnwrap (x y : Nat) : Nat :=
  match div x y with
    | .ok v    => v
    | .error _ => 0

#print divUnwrap

instance : MonadLift (Except String) IO where
  monadLift := lift where
    lift {α : Type} (t : Except String α) : IO α := do
      match t with
        | .ok v    => EStateM.Result.ok v
        | .error e => EStateM.Result.error e

def main4 : IO Unit := do
  try
    println! <- div 10 0
  catch
    e => println! s!"Unhandled Exception: {e}"

#eval main4

#check IO.Error

instance [Add α] : Add (List α) where
  add x y := .zipWith (· + ·) x y

#eval [1,2,3,4] + [5,6,7,8]


variable (α : Type)
#check ∃x : α, x = x
