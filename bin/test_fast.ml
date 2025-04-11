open ExEnum
open Printer
open PIL.Formulas
open Sys
open Char
open FastPitts
open Stringconversion
open Modal_expressions_parser
open PIL.Extraction
open PIL.DecisionProcedure


(* n first variables *)
let rec n_vars n = if n <= 1 then [['p']] else [Char.chr ((Char.code 'p') + n)] :: n_vars (n - 1)

let e_vars = from_list ~name:"variables" (n_vars 2)

(* Type term is recursive, hence we need a lazy enumeration first. *)
let rec l_e_formulas = lazy
    begin
      let r_formulas = pay l_e_formulas in
      union
	[ single (Bot Modal) ;
    map e_vars (fun x -> Var (Modal, x)) ;
	  map (pair r_formulas r_formulas) (fun (t1, t2) -> And (Modal, t1, t2)) ;
    map (pair r_formulas r_formulas) (fun (t1, t2) -> Or (Modal, t1, t2)) ;
   map (pair r_formulas r_formulas) (fun (t1, t2) -> Implies (Modal, t1, t2)) ;
   (* map r_formulas (fun x -> Box x); Don't test modal formulas for now *)
	]
    end


(* Enumeration for formulas. *)
let e_formulas = Lazy.force l_e_formulas

(* The code below prints _num_ formulas and their existential interpolant *)

let nb_args = Array.length Sys.argv

let form = if nb_args = 2 then (Sys.argv.(1)) else "T"
let start = if nb_args < 3 then 0 else int_of_string Sys.argv.(1)
let num = if nb_args < 3 then 1 else int_of_string Sys.argv.(2)

let usage_string =
"Debug only"

let v : variable = coqstring_of_camlstring "p"

let show_test (f: form) : string =
(*   let _ = print_string "computing fast_fa" in
 *)  let fast_fa = isl_simp(a v [] [] [] [] [] f) in
(*   let _ = print_string "computing fa" ; flush stdout in
 *)  let fa = isl_simplified_A v f in
(*   let _ = print_string "computing fe" in
 *)  let fe = isl_simplified_E v f in
(*   let _ = print_string "computing fast_fe" in
 *)  let fast_fe =  isl_simp(e v [] [] [] [] [] [f]) in
(*   let _ = print_string "checking" in
*)
(*
 let sfa = string_of_formula fa
 and sfe = string_of_formula fe
 and sfast_fa = string_of_formula fast_fa
 and sfast_fe = string_of_formula fast_fe in
 if weight Normal fa = weight Normal fast_fa && weight Normal fe = weight Normal fast_fe then "OK" else
  ("Difference with " ^ string_of_formula f ^ ":\n A:\n" ^
  sfa ^ "\nFast A:\n" ^ sfast_fa ^ "\n" ^
  "E: \n" ^ sfe ^ "\nFast E:\n" ^ sfast_fe ^ "\n")
  *)
  let equiva = And(Modal, Implies(Modal, fa, fast_fa), Implies(Modal, fast_fa, fa)) in
  let equive = And(Modal, Implies(Modal, fe, fast_fe), Implies(Modal, fast_fe, fe)) in
  match coq_Provable_dec Modal [] equiva, coq_Provable_dec Modal [] equive with
  | Coq_inl _,  Coq_inl _ -> "OK" | _ -> (
    "Error with " ^ string_of_formula f ^ ":\n A:\n" ^
    string_of_formula fa ^ "\nFast A:\n" ^ string_of_formula fast_fa ^ "\n" ^
    "E: \n" ^ string_of_formula fe ^ "\nFast E:\n" ^ string_of_formula fast_fe ^ "\n")

let () =
  if nb_args = 2 then print_string (show_test (eval form))
  else if nb_args < 2 then (print_string usage_string)
  else
    show e_formulas show_test start num;
