def partition (pred : α -> Bool) : List α -> List α × List α
  | []      => ([], [])
  | x :: xs =>
    let (taken, dropped) := partition pred xs
    if pred x then
      (x :: taken, dropped)
    else (taken, x :: dropped)

partial def qsort [LT α] [DecidableRel $ @LT.lt α _] : List α -> List α
  | [] => []
  | p :: xs =>
    let (smaller, otherwise) := partition (· < p) xs
    qsort smaller ++ p :: qsort otherwise

#eval qsort [2,3,4,1,2]
