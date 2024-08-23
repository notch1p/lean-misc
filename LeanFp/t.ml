(* Code for the article ``Map--monoid-reduce'' *)
(* #use "monoid_reduce.ml" *)

(* Left-to-right function composition *)
let (>>) f g = fun x -> f x |> g

(* Left and right folds are defined in the standard library, as
val fold_left  : ('z -> 'a -> 'z) -> 'z -> 'a list -> 'z
val fold_right : ('a -> 'z -> 'z) -> 'a list -> 'z -> 'z
*)

let _ = List.fold_left (+) 0 [1;2;3;4]
(*  (((0 + 1) + 2) + 3) + 4 = 10 *)

let _ = List.fold_right (+) [1;2;3;4] 0
(* 1 + (2 + (3 + (4 + 0))) = 10 *)

let _ = List.fold_left (-) 0 [1;2;3;4]
(*  (((0 - 1) - 2) - 3) - 4 = -10 *)

let _ = List.fold_right (-) [1;2;3;4] 0
(* 1 - (2 - (3 - (4 - 0))) = -2 *)

(* Many things can be expressed via fold, for example *)

let length (l:'a list) : int = List.fold_left (fun z _ -> z + 1) 0 l
let[@warning "-8"] 4 = length [1;2;3;4]

(* it has to be fold_left *)
let reverse (l:'a list) : 'a list = List.fold_left (fun z x -> x :: z) [] l
let[@warning "-8"] [4;3;2;1] = reverse [1;2;3;4]

(* it has to be fold_right *)
let filter (p:'a -> bool) (l:'a list) : 'a list =
  List.fold_right (fun x z -> if p x then x::z else z) l []
let[@warning "-8"] [2;4] = filter (fun x -> x mod 2 = 0) [1;2;3;4]
 

(* A monoid is a set with an associative binary operation defined
   on it which has a unit (also called zero) element
*)
type 'a monoid = {zero: 'a; op: 'a -> 'a -> 'a}

(* reduce over a monoid and one of its implementations *)
let rec reduce : 'a monoid -> 'a list -> 'a = fun {zero;op} -> function
  | [] -> zero
  | [x] -> x
  | h::t -> op h (reduce {zero;op} t)

let[@warning "-8"] 10 = reduce {zero=0;op=(+)} [1;2;3;4]
(* 1 + 2 + 3 + 4 *)

(* Since reduce is often pre-composed with map, we may introduce
   the fused map_reduce
 *)
let rec map_reduce : ('a -> 'z) -> 'z monoid -> 'a list -> 'z = 
  fun f ({zero;op} as m) -> function
  | [] -> zero
  | [x] -> f x
  | h::t -> op (f h) (map_reduce f m t)

(* Left-fold is just a for-loop. Here, we use an array slice 
as a collection (described as an array, the from and to indices) *)

type 'a array_slice = {arr:'a array; from:int; upto:int} 
let fold_left_arr : ('z -> 'a -> 'z) -> 'z -> 'a array_slice -> 'z = 
  fun f z {arr;from;upto} ->
  let acc = ref z in
  for i=from to upto do
    acc := f !acc arr.(i)
  done;
  !acc

let whole_slice (arr:'a array) : 'a array_slice = 
  {arr; from=0; upto=Array.length arr -1}

let[@warning "-8"] 28 = fold_left_arr (+) 0 (whole_slice [|1;2;3;4;5;6;7|])

(* summing [1..100] *)
let[@warning "-8"] 5050 = 
   Array.init 100 succ |> whole_slice |> fold_left_arr (+) 0

(* reduce over an array can also be done sequentially:
   reduce can be implemented via fold
 *)
let seqreduce_arr (m: 'a monoid) (arrsl: 'a array_slice) : 'a =
  fold_left_arr m.op m.zero arrsl

let[@warning "-8"] 5050 = 
   Array.init 100 succ |> whole_slice |> seqreduce_arr {zero=0;op=(+)}

(* The reduce over an array can also be implemented as hierarchical
   decomposition
*)
let rec parreduce_arr (m: 'a monoid) {arr;from;upto} : 'a =
  match upto+1-from with
  | 0 -> m.zero
  | 1 -> arr.(from)
  | 2 -> m.op arr.(from) arr.(from+1)
  | 3 -> m.op (m.op arr.(from) arr.(from+1)) arr.(from+2)
  | n -> let n' = n / 2 in
         (* Here, the two parreduce_arr invocations can be done in parallel! *)
         m.op 
           (parreduce_arr m {arr;from;upto=from+n'-1})
           (parreduce_arr m {arr;from=from+n';upto})

let t = parreduce_arr {zero=0;op=(+)} (whole_slice [|1;2;3;4;5;6;7;8;9;10|])

let[@warning "-8"] 5050 = 
   Array.init 100 succ |> whole_slice |> parreduce_arr {zero=0;op=(+)}

(* partition across two cores *)
let reduce_2cores (m:'a monoid) 
    (subreducer: 'a monoid -> 'a array_slice -> 'a) {arr;from;upto} : 'a =
  let len = upto+1-from in
  if len < 10 (* too-short thershold *)
     then subreducer m {arr;from;upto} 
     else let n' = len / 2 in
       m.op (* in parallel *)
       (subreducer m {arr;from;upto=from+n'-1})
       (subreducer m {arr;from=from+n';upto})

let[@warning "-8"] 5050 = Array.init 100 succ |> whole_slice |> 
   reduce_2cores {zero=0;op=(+)} seqreduce_arr

(* fold in terms of reduce *)
let compose_monoid = {op=(fun g h -> fun x -> g (h x)); zero=Fun.id}
let fold_reduce_triv = fun f z l ->
  List.fold_right f l z =
  (List.map f l |> reduce compose_monoid |> (|>) z)

let[@warning "-8"] true = fold_reduce_triv (-) 10 [1;2;3;4]

let fold_reduce = fun f z l ->
  List.fold_left f z l =
  (List.map (fun x -> (fun z -> f z x)) l |> reduce compose_monoid |> (|>) z)

(* Simple reductions *)
let length (l:'a list) : int = 
  (* List.fold_left (fun z _ -> z + 1) 0 l *)
  List.map (Fun.const 1) l |> reduce {op=(+);zero=0}
let[@warning "-8"] 4 = length [1;2;3;4]
let length (l:'a list) : int = 
  (* List.fold_left (fun z _ -> z + 1) 0 l *)
  map_reduce (Fun.const 1) {op=(+);zero=0} l
let[@warning "-8"] 4 = length [1;2;3;4]

(* Here we need efficient append *)
let reverse (l:'a list) : 'a list = 
  (* List.fold_left (fun z x -> x :: z) [] l *)
  map_reduce (fun x -> [x]) {op=(Fun.flip (@));zero=[]} l
let[@warning "-8"] [4;3;2;1] = reverse [1;2;3;4]

(* it has to be fold_right *)
let filter (p:'a -> bool) (l:'a list) : 'a list =
  (* List.fold_right (fun x z -> if p x then x::z else z) l [] *)
  map_reduce (fun x -> if p x then [x] else []) {op=(@);zero=[]} l
let[@warning "-8"] [2;4] = filter (fun x -> x mod 2 = 0) [1;2;3;4]


(* fold_left (-) l z as monoid reduction *)

let foldl_sub = fun z l ->
  List.fold_left (-) z l =
  (reduce {op=(+);zero=0} l |> (-) z)

let[@warning "-8"] true = foldl_sub 5 []
let[@warning "-8"] true = foldl_sub 5 [1]
let[@warning "-8"] true = foldl_sub 10 [1;2;3;4]
let[@warning "-8"] true = foldl_sub 0 [1;2;3;4;4;3;2;1]
let[@warning "-8"] true = foldl_sub 10 (List.init 100 succ)
let[@warning "-8"] true = foldl_sub (-1) (List.init 100 succ |> List.rev)

(* fold_right (-) l z as monoid reduction *)

let sub_monoid = {zero=(0,true); 
                  op = fun (a,aeven) (b,beven) ->
                       ((if aeven then a + b else a - b), aeven = beven)}

let foldr_sub = fun l ->
  List.fold_right (-) l 0 =
  (List.map (fun a -> (a,false)) l |> reduce sub_monoid |> fst)

let[@warning "-8"] true = foldr_sub []
let[@warning "-8"] true = foldr_sub [1]
let[@warning "-8"] true = foldr_sub [1;2;3;4]
let[@warning "-8"] true = foldr_sub [1;2;3;4;4;3;2;1]
let[@warning "-8"] true = foldr_sub (List.init 100 succ)
let[@warning "-8"] true = foldr_sub (List.init 100 succ |> List.rev)

(* ------------------------------------------------------------------------
   Horner rule 
*)

let digits_to_num = 
  List.fold_left (fun z x -> 10*z + (Char.code x - Char.code '0')) 0

let[@warning "-8"] 175 = digits_to_num ['1'; '7'; '5']

let digits_to_num = 
  List.map (fun x -> Char.code x - Char.code '0') >>
  List.fold_left (fun z x -> 10*z + x) 0

let[@warning "-8"] 175 = digits_to_num ['1'; '7'; '5']

let horner_monoid =
  {op = (fun (x,b1) (y,b2) -> (x*b2+y, b1*b2));
   zero = (0,1)}

let digits_to_num = 
  List.map (fun x -> Char.code x - Char.code '0') >>
  List.map (fun x -> (x,10)) >>
  reduce horner_monoid >> fst

let[@warning "-8"] 175 = digits_to_num ['1'; '7'; '5']

(* Using array, for better testing *)
let digits_to_num = 
  Array.map (fun x -> Char.code x - Char.code '0') >>
  Array.map (fun x -> (x,10)) >>
  whole_slice >>
  parreduce_arr horner_monoid >> fst

let[@warning "-8"] 0 = digits_to_num [||]
let[@warning "-8"] 5 = digits_to_num [|'5'|]
let[@warning "-8"] 17503 = digits_to_num [|'1'; '7'; '5'; '0'; '3'|]
let[@warning "-8"] 17503 = digits_to_num [|'0'; '1'; '7'; '5'; '0'; '3'|]

(* generalization *)
let hmonoid (m:'a monoid) : ('a * ('a->'a)) monoid = 
  {op = (fun (x,h1) (y,h2) -> (m.op (h2 x) y, h1 >> h2));
   zero = (m.zero, Fun.id)}

let digits_to_num = 
  Array.map (fun x -> Char.code x - Char.code '0') >>
  Array.map (fun x -> (x,fun x -> x * 10)) >>
  whole_slice >>
  parreduce_arr (hmonoid {op=(+);zero=0}) >> fst

let[@warning "-8"] 0 = digits_to_num [||]
let[@warning "-8"] 5 = digits_to_num [|'5'|]
let[@warning "-8"] 17503 = digits_to_num [|'1'; '7'; '5'; '0'; '3'|]
let[@warning "-8"] 17503 = digits_to_num [|'0'; '1'; '7'; '5'; '0'; '3'|]

(* ------------------------------------------------------------------------
   Boyer-Moore majority algorithm 
   Finding an element that occurs more than half the time in a collection
   (sequence)
*)

(* The algorithm as typically presented: sequential
   See Wipipedia
*)

(* assume the argument list is non-empty *)
let bm' : 'a list -> (int * 'a) = function 
  | h::t -> let fsm (c,m) x =
      if c = 0 then (1,x)
      else if m = x then (c+1,m)
      else (c-1,m)
  in List.fold_left fsm (1,h) t
  | _    -> failwith "empty list"

let bm : 'a list -> 'a =  fun l -> bm' l |> snd 

(* Sample sequence, from Wikipedia *)
let bm_ex1 = [1;1;2;1;2;3;3;2;2;2;1;2;2;3;2;2]
let[@warning "-8"] (4,2) = bm' bm_ex1

let repeat : int -> 'a -> 'a list = fun n x -> List.init n (Fun.const x)

(* regression tests *)
(* no majority *)
let[@warning "-8"] (0,4) = bm' (repeat 4 4 @ repeat 4 5)
let[@warning "-8"] (3,5) = bm' (repeat 4 4 @ repeat 3 3 @ repeat 4 5)
let[@warning "-8"] (1,5) = bm' (repeat 4 [4;5] |> List.concat |> (@) [3])
(* majority: 5 *)
let[@warning "-8"] (1,5) = bm' (repeat 4 [4;5] |> List.concat |> (@) [5])
let[@warning "-8"] (4,5) = bm' (repeat 5 5 @ [1])


(* z is an arbitrary element (an arbitrary member of element type)
   We could have build monoid over the 'a option type ('a being the
   type of sequence elements). Then z would be None.
   For many domains, however, there is a suitable arbitrary element, e.g.,
   0, '\000', etc.
   Mainly, the following definition is slightly easier to use when
   explaining formalization. 
 *)
let bm_monoid (z:'a) : (int * 'a) monoid = 
  {zero = (0,z);
   op = fun (c1,m1) (c2,m2) ->
     if c1 = 0 then (c2,m2) else
     if c2 = 0 then (c1,m1) else
     if m1 = m2 then (c1+c2,m1) else
     if c1 > c2 then (c1-c2, m1) else
     (c2-c1, m2)}

(* Boyer-Moore as map-reduce *)
let bm_red =  
  Array.of_list >>
  Array.map (fun x -> (1,x)) >>
  whole_slice >>
  parreduce_arr (bm_monoid 0)

(* regression tests *)
let[@warning "-8"] (2,2) = bm_red bm_ex1

let[@warning "-8"] (0,5) = bm_red (repeat 4 4 @ repeat 4 5)
let[@warning "-8"] (1,4) = bm_red (repeat 4 4 @ repeat 3 3 @ repeat 4 5)
let[@warning "-8"] (1,5) = bm_red (repeat 4 [4;5] |> List.concat |> (@) [3])
(* majority: 5 *)
let[@warning "-8"] (1,5) = bm_red (repeat 4 [4;5] |> List.concat |> (@) [5])
let[@warning "-8"] (4,5) = bm_red (repeat 5 5 @ [1])

(* bm_monoid is surely commutative. But is it actually monoid?
   That is, is op associative?
*)

let[@warning "-8"] ((1, 8), (1, 10))
 =
  let m1 = (2,10) and m2 = (3,9) and m3 = (2,8) in
  let op = (bm_monoid 0).op in
  (
   op (op m1 m2) m3,
   op m1 (op m2 m3)
  )


(* Extended bm_monoid
The third component is a list of pairs with distinct components
(that is, fst of any pair is not equal to its snd)
*)
let bm_monoid_ext (z:'a) : (int * 'a * ('a*'a) list) monoid = 
  {zero = (0,z,[]);
   op = fun (c1,m1,l1) (c2,m2,l2) ->
     if c1 = 0 then (c2,m2,l1@l2) else
     if c2 = 0 then (c1,m1,l1@l2) else
     if m1 = m2 then (c1+c2,m1,l1@l2) else
     if c1 > c2 then (c1-c2, m1, repeat c2 (m1,m2) @ l1 @ l2) else
     (c2-c1, m2, repeat c1 (m1,m2) @ l1 @ l2)}

(* An element of bm_monoid_ext as a multiset *)
let bm_flatten : (int * 'a * ('a*'a) list) -> 'a list = fun (c,m,l) ->
  repeat c m @ List.map fst l @ List.map snd l

(* A special equality on the carrier set: essentially, multiset equality *)
let bm_eq : (int * 'a * ('a*'a) list) -> (int * 'a * ('a*'a) list) -> bool =
  fun x y -> List.sort compare (bm_flatten x) = List.sort compare (bm_flatten y)

let[@warning "-8"] 
 ((1, 8,
  [(9, 8); (10, 9); (10, 9); (9, 10); (8, 9); (9, 10); (9, 10); (8, 10)]),
 (1, 10,
  [(10, 9); (9, 10); (9, 8); (9, 8); (8, 9); (9, 10); (9, 10); (8, 10)]))
 =
  let m1 = (2,10,[(9,10)]) and m2 = (3,9,[(8,9);(9,10)]) and 
      m3 = (2,8,[(9,10);(8,10)]) in
  let op = (bm_monoid_ext 0).op in
  (
   op (op m1 m2) m3,
   op m1 (op m2 m3)
  )

(* That is, bm_monoid_ext is a monoid, modulo bm_eq *)
let[@warning "-8"] 
 true
 =
  let m1 = (2,10,[(9,10)]) and m2 = (3,9,[(8,9);(9,10)]) and 
      m3 = (2,8,[(9,10);(8,10)]) in
  let op = (bm_monoid_ext 0).op in
  (
   bm_eq (op (op m1 m2) m3) 
         (op m1 (op m2 m3))
  )

;;