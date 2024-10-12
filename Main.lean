import «LeanFp»

structure Environment where
  path : String
  home : String
  user : String
deriving Repr

def getEnvDefault (name : String): IO String := do
  let val? ← IO.getEnv name
  pure <| match val? with
          | none => ""
          | some s => s

def loadEnv : IO Environment := do
  let path ← getEnvDefault "PATH"
  let home ← getEnvDefault "HOME"
  let user ← getEnvDefault "USER"
  pure { path, home, user }

def readerFunc1 : StateM Environment Float := do
  let env ← get
  let l1 := env.path.length
  let l2 := env.home.length * 2
  let l3 := env.user.length * 3
  return (l1 + l2 + l3).toFloat * 2.1

def readerFunc2 : StateM Environment Nat :=
  readerFunc1 >>= (fun x => return 2 + (x.floor.toUInt32.toNat))

def readerFunc3 : StateM Environment String := do
  let x ← readerFunc2
  return "Result: " ++ toString x

def main2 : IO Unit := do
  let env ← loadEnv
  let str := readerFunc3.run env
  IO.println str.1

#eval main2 -- Result: 7538

#reduce (types := true) StateM Environment String

#reduce (types := true) ReaderM Environment String


#check ∃ x : ℕ, x = 1

#check Unit
