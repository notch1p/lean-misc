def firstIndexOf? [BEq α] (elem : α) : List α -> Nat -> Option Nat
  | [], _ => none
  | x :: xs, idx =>
    if x == elem then
      some idx
    else
      firstIndexOf? elem xs (idx + 1)

abbrev Args := List String

def getRequiredArg (name : String) : ReaderT Args (Except String) String := do
  let args <- read
  let v : String := match firstIndexOf? name args 0 with
    | some i => if i + 1 < args.length then args[i + 1]! else ""
    | none => ""
  if v == "" then throw s!"required argument '{name}' is missing"
  return v

def getOptionalArg (name : String) : ReaderT Args (Except String) Bool := do
  let args <- read
  return match firstIndexOf? name args 0 with
    | some _ => true
    | none => false

#eval getRequiredArg "--foo" ["--foo", "bla", "--bar", "bla"]

#eval getOptionalArg "--foo" ["--foo", "bla", "--bar", "bla"]

structure Config where
  foo : Bool := false
  bar : String := ""
  help : Bool := false
deriving Repr

abbrev ConfigM := StateT Config (ReaderT Args (Except String))

#reduce (types := true) ReaderT Args (Except String)

def parseArgs : ConfigM Bool := do
  let mut config <- get
  if (<- getOptionalArg "--help") then
    throw "Usage: ..."
  config := {
    config with
    foo := (<- getOptionalArg "--foo"),
    bar := (<- getRequiredArg "--bar")
  }
  set config
  pure true

instance : ToString Config where
  toString c := s!"[foo := {c.foo}, bar := {c.bar}, help := {c.help}]"

def liftIO (t : Except String α) : IO α :=
  match t with
   | .ok v => EStateM.Result.ok v
   | .error e => EStateM.Result.error e

#reduce (types := true) liftIO

instance : MonadLift (Except String) IO where
  monadLift := liftIO

def printArgs : IO Unit := do
  try
    let args <- parseArgs |>.run {} |>.run ["--help", "--foo", "--bar", "bla"]
    IO.println args.2
  catch e => IO.println e

#eval printArgs


#eval parseArgs |>.run {} |>.run ["--foo", "--bar", "bla"]

def liftTest (x : Except String Nat) : StateT Nat (Except String) Nat := monadLift x

#print liftTest

#check liftM

#check StateT.lift
