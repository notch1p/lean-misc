import «LeanFp»

structure Env where
  path : String
  home : String
  user : String
deriving Repr

def getEnv (name : String) : IO String := do
  let val? <- IO.getEnv name
  pure <| match val? with
    | some val => val
    | none     => "<not set>"

def loadEnv : IO Env := do
  let path <- getEnv "PATH"
  let home <- getEnv "HOME"
  let user <- getEnv "USER"
  pure { path, home, user }

def main : IO Unit := do
  let env <- loadEnv
  IO.println s!"home := {env.home}"
  IO.println s!"user := {env.user}"
  IO.println s!"path := {env.path}"
