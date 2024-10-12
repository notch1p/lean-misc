inductive Tree (α : Type)
  | TNil
  | TNode: α -> Tree α -> Tree α -> Tree α

def String.repeat : String -> Nat -> String
  | _, 0     => ""
  | s, n + 1 => s ++ String.repeat s n

def Tree.pretty [ToString α] : Tree α -> Nat -> String
  | TNil, _ => ""
  | TNode val left right, indent =>
    let indentStr := String.repeat "  " indent
    s!"{indentStr}{val}\n" ++ pretty left (indent + 1) ++ pretty right (indent + 1)

open Tree in
#eval let tree := TNode 1 (TNode 2 (TNode 3 TNil TNil) TNil) (TNode 4 (TNode 5 TNil TNil) TNil)
println! tree.pretty 0
/-
1
  2
    3
  4
    5
-/
