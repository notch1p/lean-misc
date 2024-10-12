inductive Tree (α : Type) where
  | empty
  | node : Tree α -> α -> Tree α -> Tree α
deriving Repr


def deep : Nat -> Tree Nat
  | 0 => .empty
  | n + 1 => let t := deep n; .node t n t

def iter (f : α -> Unit) (t : Tree α) :=
  match t with
  | .empty => ()
  | .node l x r =>
    let _ := (iter f l, f x, iter f r);
    ()

#check ForIn

#check List.foldl
#check match (1,'c',true) with | (a,_,b) => (a,b)
