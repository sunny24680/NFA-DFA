open Sets
open Nfa

(*********)
(* Types *)
(*********)

type regexp_t =
  | Empty_String
  | Char of char
  | Union of regexp_t * regexp_t
  | Concat of regexp_t * regexp_t
  | Star of regexp_t

(*******************************)
(* Part 2: Regular Expressions *)
(*******************************)
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

let rec t_changes amt deltas = 
  match deltas with 
  | [] -> []
  | (a,d,s)::t -> (a+amt,d,s+amt)::t_changes amt t

let new_states m1 m2 = 
  let l1 = List.length m1.qs in 
    let qs' = List.map (fun elt -> elt + l1) m2.qs in 
      let deltas' = t_changes l1 m2.delta in
        {qs = qs'; sigma = m2.sigma; delta = deltas'; q0=m2.q0+l1; fs= [(List.hd m2.fs) + l1]}  

let rec regexp_to_nfa re = 
  match re with 
  | Empty_String -> 
    {qs=[0]; 
    sigma=[]; 
    delta=[(0,None,0)]; 
    q0 = 0;
    fs=[0]}
  | Char(c) -> 
    {qs=[1;2]; 
    sigma=[c]; 
    delta= [(1,Some c,2)]; 
    q0 = 1; 
    fs=[2]}
  | Union(a,b) -> 
    let r1 = regexp_to_nfa a in 
      let r2 = regexp_to_nfa b in 
        let nr2 = new_states r1 r2 in
          let l2 = List.length nr2.qs in 
            let l1 = List.length r1.qs in
              {qs = union (union r1.qs nr2.qs) [1+l1+l2;2+l1+l2]; 
              sigma = union r1.sigma nr2.sigma; 
              delta = union (union r1.delta nr2.delta) [(1+l1+l2,None,r1.q0); (1+l1+l2,None,nr2.q0); ((List.hd r1.fs),None,2+l1+l2); ((List.hd nr2.fs),None,2+l1+l2)];
              q0 = 1+l1+l2;
              fs = [2+l1+l2]}  
  | Concat(a,b) -> 
    let r1 = regexp_to_nfa a in 
      let r2 = new_states r1 (regexp_to_nfa b) in
        {qs = union r1.qs r2.qs; 
        sigma = union r1.sigma r2.sigma;
        delta = union (union r1.delta r2.delta) [(List.hd r1.fs,None,r2.q0)];
        q0 = r1.q0;
        fs = r2.fs}
  | Star(r) -> 
    let n_f = regexp_to_nfa r in 
      let nf_length = List.length n_f.qs in 
        {qs = union n_f.qs [(1+nf_length);(2+nf_length)];
        sigma = n_f.sigma;
        delta = union n_f.delta [(1+nf_length,None,n_f.q0); (1+nf_length,None,2+nf_length); (List.hd n_f.fs,None,2+nf_length); (2+nf_length,None,1+nf_length)];
        q0 = 1+nf_length;
        fs = [2+nf_length]}
;;

let rec reg_to_str_h r = 
  match r with 
  | Empty_String -> "E"
  | Char t -> String.make 1 t
  | Union (h,t) -> "("^reg_to_str_h h^"|"^reg_to_str_h t^")"
  | Concat (h,t) -> "("^reg_to_str_h h^reg_to_str_h t^")"
  | Star h -> "("^reg_to_str_h h^")*"
;;

let regexp_to_string r = 
  reg_to_str_h r
;;

(*****************************************************************)
(* Below this point is parser code that YOU DO NOT NEED TO TOUCH *)
(*****************************************************************)

exception IllegalExpression of string

(* Scanner *)
type token =
  | Tok_Char of char
  | Tok_Epsilon
  | Tok_Union
  | Tok_Star
  | Tok_LParen
  | Tok_RParen
  | Tok_END

let tokenize str =
  let re_var = Str.regexp "[a-z]" in
  let re_epsilon = Str.regexp "E" in
  let re_union = Str.regexp "|" in
  let re_star = Str.regexp "*" in
  let re_lparen = Str.regexp "(" in
  let re_rparen = Str.regexp ")" in
  let rec tok pos s =
    if pos >= String.length s then
      [Tok_END]
    else begin
      if (Str.string_match re_var s pos) then
        let token = Str.matched_string s in
        (Tok_Char token.[0])::(tok (pos+1) s)
      else if (Str.string_match re_epsilon s pos) then
        Tok_Epsilon::(tok (pos+1) s)
      else if (Str.string_match re_union s pos) then
        Tok_Union::(tok (pos+1) s)
      else if (Str.string_match re_star s pos) then
        Tok_Star::(tok (pos+1) s)
      else if (Str.string_match re_lparen s pos) then
        Tok_LParen::(tok (pos+1) s)
      else if (Str.string_match re_rparen s pos) then
        Tok_RParen::(tok (pos+1) s)
      else
        raise (IllegalExpression("tokenize: " ^ s))
    end
  in
  tok 0 str

let tok_to_str t = ( match t with
      Tok_Char v -> (Char.escaped v)
    | Tok_Epsilon -> "E"
    | Tok_Union -> "|"
    | Tok_Star ->  "*"
    | Tok_LParen -> "("
    | Tok_RParen -> ")"
    | Tok_END -> "END"
  )

(*
   S -> A Tok_Union S | A
   A -> B A | B
   B -> C Tok_Star | C
   C -> Tok_Char | Tok_Epsilon | Tok_LParen S Tok_RParen

   FIRST(S) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(A) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(B) = Tok_Char | Tok_Epsilon | Tok_LParen
   FIRST(C) = Tok_Char | Tok_Epsilon | Tok_LParen
 *)

let parse_regexp (l : token list) =
  let lookahead tok_list = match tok_list with
      [] -> raise (IllegalExpression "lookahead")
    | (h::t) -> (h,t)
  in

  let rec parse_S l =
    let (a1,l1) = parse_A l in
    let (t,n) = lookahead l1 in
    match t with
      Tok_Union -> (
        let (a2,l2) = (parse_S n) in
        (Union (a1,a2),l2)
      )
    | _ -> (a1,l1)

  and parse_A l =
    let (a1,l1) = parse_B l in
    let (t,n) = lookahead l1 in
    match t with
      Tok_Char c ->
      let (a2,l2) = (parse_A l1) in (Concat (a1,a2),l2)
    | Tok_Epsilon ->
      let (a2,l2) = (parse_A l1) in (Concat (a1,a2),l2)
    | Tok_LParen ->
      let (a2,l2) = (parse_A l1) in (Concat (a1,a2),l2)
    | _ -> (a1,l1)

  and parse_B l =
    let (a1,l1) = parse_C l in
    let (t,n) = lookahead l1 in
    match t with
      Tok_Star -> (Star a1,n)
    | _ -> (a1,l1)

  and parse_C l =
    let (t,n) = lookahead l in
    match t with
      Tok_Char c -> (Char c, n)
    | Tok_Epsilon -> (Empty_String, n)
    | Tok_LParen ->
      let (a1,l1) = parse_S n in
      let (t2,n2) = lookahead l1 in
      if (t2 = Tok_RParen) then
        (a1,n2)
      else
        raise (IllegalExpression "parse_C 1")
    | _ -> raise (IllegalExpression "parse_C 2")
  in
  let (rxp, toks) = parse_S l in
  match toks with
  | [Tok_END] -> rxp
  | _ -> raise (IllegalExpression "parse didn't consume all tokens")

let string_to_regexp str = parse_regexp @@ tokenize str

let string_to_nfa str = regexp_to_nfa @@ string_to_regexp str
