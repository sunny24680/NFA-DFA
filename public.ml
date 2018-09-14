open OUnit2
open Nfa
open Regexp
open TestUtils

let test_nfa_accept ctxt =
  let m1 = { qs = [0;1]; sigma = ['a'; 'b']; delta = [(0, Some 'a', 1)]; q0 = 0; fs = [1] } in
  assert_nfa_deny m1 "";
  assert_nfa_accept m1 "a";
  assert_nfa_deny m1 "b";
  assert_nfa_deny m1 "ba";

  let m2 = { qs = [0;1;2]; sigma=['a';'b']; delta = [(0, Some 'a', 1); (0, Some 'b', 2)]; q0 = 0; fs = [2]} in
  assert_nfa_deny m2 "";
  assert_nfa_deny m2 "a";
  assert_nfa_accept m2 "b";
  assert_nfa_deny m2 "ba"

let test_nfa_to_dfa ctxt =
  let m1 = { qs = [0;1;2;3]; sigma = ['a';'b']; delta = [(0, Some 'a', 1); (0, Some 'a', 2); (2, Some 'b', 3)]; q0 = 0; fs = [1;3] } in
  let m1' = nfa_to_dfa m1 in
  assert_dfa m1';
  assert_nfa_deny m1' "";
  assert_nfa_accept m1' "a";
  assert_nfa_accept m1' "ab";
  assert_nfa_deny m1' "b";
  assert_nfa_deny m1' "ba";

  let m2 = { qs = [0;1;2]; sigma=['a';'b']; delta = [(0, Some 'a', 1); (0, Some 'b', 2)]; q0 = 0; fs = [2]} in
  let m2' = nfa_to_dfa m2 in
  assert_dfa m2';
  assert_nfa_deny m2' "";
  assert_nfa_deny m2' "a";
  assert_nfa_accept m2' "b";
  assert_nfa_deny m2' "ba"

let test_nfa_closure ctxt =
  let m1 = { qs = [0;1]; sigma = ['a']; delta = [(0, Some 'a', 1)]; q0 = 0; fs = [1] } in
  assert_nfa_closure m1 [0] [0];
  assert_nfa_closure m1 [1] [1];

  let m2 = {qs = [0;1]; sigma=[]; q0=0; delta=[(0, None, 1)]; fs=[1]; } in
  assert_nfa_closure m2 [0] [0;1];
  assert_nfa_closure m2 [1] [1];

  let m3 = {qs = [0;1;2]; sigma=['a';'b']; q0=0; fs=[2]; delta=[(0, Some 'a', 1); (0, Some 'b', 2)]} in
  assert_nfa_closure m3 [0] [0];
  assert_nfa_closure m3 [1] [1];
  assert_nfa_closure m3 [2] [2];

  let m4 = {qs = [0;1;2]; sigma=['a']; q0=0; fs=[2]; delta=[(0, None, 1); (0, None, 2)]} in
  assert_nfa_closure m4 [0] [0;1;2];
  assert_nfa_closure m4 [1] [1];
  assert_nfa_closure m4 [2] [2]

let test_nfa_move ctxt =
  let m1 = { qs = [0;1]; sigma = ['a']; delta = [(0, Some 'a', 1)]; q0 = 0; fs = [1] } in
  assert_nfa_move m1 [0] (Some 'a') [1];
  assert_nfa_move m1 [1] (Some 'a') [];

  let m2 = { qs = [0;1]; sigma = ['a']; delta = [(0, None, 1)]; q0 = 0; fs = [1] } in
  assert_nfa_move m2 [0] (Some 'a') [];
  assert_nfa_move m2 [1] (Some 'a') [];

  let m3 = {qs = [0;1;2]; sigma=['a';'b']; q0=0; fs=[2]; delta=[(0, Some 'a', 1); (0, Some 'b', 2)]} in
  assert_nfa_move m3 [0] (Some 'a') [1];
  assert_nfa_move m3 [1] (Some 'a') [];
  assert_nfa_move m3 [2] (Some 'a') [];
  assert_nfa_move m3 [0] (Some 'b') [2];
  assert_nfa_move m3 [1] (Some 'b') [];
  assert_nfa_move m3 [2] (Some 'b') [];

  let m4 = {qs = [0;1;2]; sigma=['a';'b']; q0=0; fs=[2]; delta=[(0, None, 1); (0, Some 'a', 2)]} in
  assert_nfa_move m4 [0] (Some 'a') [2];
  assert_nfa_move m4 [1] (Some 'a') [];
  assert_nfa_move m4 [2] (Some 'a') [];
  assert_nfa_move m4 [0] (Some 'b') [];
  assert_nfa_move m4 [1] (Some 'b') [];
  assert_nfa_move m4 [2] (Some 'b') []

let test_re_to_nfa ctxt =
  let m1 = regexp_to_nfa (Char('a')) in
  assert_nfa_deny m1 "";
  assert_nfa_accept m1 "a";
  assert_nfa_deny m1 "b";
  assert_nfa_deny m1 "ba";

  let m2 = regexp_to_nfa (Union(Char('a'), Char('b'))) in
  assert_nfa_deny m2 "";
  assert_nfa_accept m2 "a";
  assert_nfa_accept m2 "b";
  assert_nfa_deny m2 "ba"

let test_re_to_str ctxt =
  let r1 = Concat(Char('a'), Char('b')) in
  assert_regex_string_equiv r1;

  let r2 = Union(Char('c'), Char('d')) in
  assert_regex_string_equiv r2;

  let r3 = Star(Char('e')) in
  assert_regex_string_equiv r3

let test_str_to_nfa ctxt =
  let m1 = regexp_to_nfa @@ string_to_regexp "ab" in
  assert_nfa_deny m1 "a";
  assert_nfa_deny m1 "b";
  assert_nfa_accept m1 "ab";
  assert_nfa_deny m1 "bb"

let test_fuck_off ctxt = 
  let m = regexp_to_nfa @@ string_to_regexp "a*" in
  assert_nfa_accept m "";
  assert_nfa_accept m "a";
  assert_nfa_deny m "b";

  let m' = nfa_to_dfa m in 
  assert_nfa_accept m' "";
  assert_nfa_accept m' "a";
  assert_nfa_deny m' "b";

  let m = regexp_to_nfa @@ string_to_regexp "(a|E)*(a|b)" in 
  assert_nfa_accept m "a";
  assert_nfa_deny m "";
  assert_nfa_accept m "aaaaaaab";
  assert_nfa_accept m "b";

  let m = regexp_to_nfa @@ string_to_regexp "(bc|ad)*" in 
  assert_nfa_accept m "ad";
  assert_nfa_deny m "ab";
  assert_nfa_accept m "";
  assert_nfa_accept m "adadad";
  assert_nfa_accept m "adbc";

  let q = { qs = [0;1;2;3;4;5;6;7;8;9]; sigma = ['a'; 'b']; delta = [(0, Some 'a', 1); (1, None, 2); (2, None, 3); (3, None, 4); (4, None, 5); (5, None, 6); (6, None, 7); (7, None, 8); (8, None, 9)]; q0 = 0; fs = [9] } in
  assert_nfa_accept q "a";
  assert_nfa_deny q "b";
  assert_nfa_deny q "";

  let m1 = { qs = [0;1;2;3]; sigma = ['a';'b']; delta = [(0, Some 'a', 1); (0, Some 'a', 2); (2, Some 'b', 3); (2, Some 'a', 3); (3, Some 'a', 1)]; q0 = 0; fs = [1;3] } in
  assert_nfa_move m1 [0;3] (Some 'a') [1;2]

let suite =
  "public" >::: [
    "nfa_accept" >:: test_nfa_accept;
    "nfa_closure" >:: test_nfa_closure;
    "nfa_move" >:: test_nfa_move;
    "nfa_to_dfa" >:: test_nfa_to_dfa;
    "re_to_nfa" >:: test_re_to_nfa;
    "re_to_str" >:: test_re_to_str;
    "str_to_nfa" >:: test_str_to_nfa;
    "fuck_off" >:: test_fuck_off
  ]

let _ = run_test_tt_main suite
