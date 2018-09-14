open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q
type ('q, 's) nfa_t = {
  qs : 'q list;
  sigma : 's list;
  delta : ('q, 's) transition list;
  q0 : 'q;
  fs : 'q list;
}

(*********************)
(* Utility Functions *)
(*********************)

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let rec fix comp f x0 =
  let next = f x0 in
  if comp x0 next then x0 else fix comp f next

let rec elem x a = 
  match a with
  | [] -> false
  | h::t -> if h = x then true 
  else elem x t
;;

let rec insert x a = 
  if elem x a = true then a 
  else x::a
;;

let rec union a b = 
  match a with 
  | f::tail -> if (elem f (union tail b)) = false then 
  insert f (union tail b)
  else
  (union tail b)
  | [] -> match b with 
    | [] -> []
    | h::t -> if (elem h (union a t)) = false then 
    insert h (union a t)
    else
    (union a t)
;;

let rec subset a b = 
  match a with
  | [] -> true
  | h::t -> if (elem h b) = true then subset t b 
  else false
;;

let rec eq a b = 
  if (subset a b) = true then 
    if (subset b a) = true then true 
    else false
  else false
;;

(****************)
(* Part 1: NFAs *)
(****************)

let rec move_h delta q s = 
  match delta with 
  | [] -> []
  | h::t -> match h with 
    | (start,trans,finish) -> if (start = q && trans = s) then 
      union [finish] (move_h t q s)
    else move_h t q s
;;

let rec move_h1 m qs s = 
  match qs with 
  | [] -> []
  | h::t -> union (move_h m.delta h s) (move_h1 m t s)
;;

let move m qs s = 
  move_h1 m qs s
;;

let rec e_clo_h m qs l= 
  match qs with 
  | [] -> []
  | h::t -> if (List.mem h l) = false then 
    let ep = move_h m.delta h None in 
      [h]@e_clo_h m (t@ep) (l@[h])
  else e_clo_h m t l
;;

let e_closure m qs = 
  e_clo_h m qs []
;;

let rec contains l1 l2 =  
  match l1 with 
  | [] -> false
  | h::t -> if (List.mem h l2) then true else contains t l2 
;;

let rec accept_h m loc input = 
  match input with 
  | [] -> let moves = (e_closure m loc) in 
    if (contains moves m.fs) then true else false
  | h::t -> accept_h m (move m (e_closure m loc) (Some h)) t
;;

let accept m str = 
  accept_h m ([m.q0]) (explode str)
;;

let rec find_final m states = 
  match states with 
  | [] -> []
  | h::t -> if contains m.fs h then 
    h::find_final m t
  else find_final m t
;;

let rec temp m sigma loc = 
  match sigma with 
  | [] -> []
  | h'::t' -> if (move m (e_closure m loc) (Some h')) != [] then 
    ((e_closure m loc), (Some h'), e_closure m (move m (e_closure m loc) (Some h')))::temp m t' loc
  else 
    temp m t' loc
;;

let rec possible_t m loc = 
  match loc with 
  | [] -> []
  | h::t -> temp m m.sigma h@possible_t m t
;;

let rec transition_h m unmarked = 
  match unmarked with 
  | [] -> []
  | h::t -> possible_t m h@(transition_h m t)
;;

let rec possible_m m moves loc= 
  match moves with 
  | [] -> []
  | h::t -> e_closure m (move m (e_closure m loc) (Some h))::possible_m m t loc
;;

let rec state_h m marked unmarked = 
  match unmarked with 
  | [] -> marked
  | h::t -> if (List.mem h marked) = false then 
    let unmark = possible_m m m.sigma h in 
      state_h m (marked@[h]) (t@unmark)
  else state_h m marked t 
;;

let nfa_to_dfa m = 
  let r0 = e_closure m [m.q0] in 
    let states = state_h m [] [r0] in 
      let transition = transition_h m [states] in 
        let final = find_final m states in 
          let dfa = {qs = states; sigma = m.sigma; delta = transition; q0 = r0; fs = final} in 
            dfa
;;


