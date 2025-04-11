open PIL.Formulas
open PIL.Extraction
open Printer

let top = Implies(Normal, Bot Normal, Bot Normal)
let bot = Bot Normal


(* tries to apply modus ponens for a variable and place the variable in the relevant stack *)
let try_var_mp q (imp_vars, stack) f = match f with
  | Implies(_, Var(_, q'), f') when q = q' ->
      (imp_vars, f' :: stack)
  | _ -> (f :: imp_vars, stack)

let conj a b = match a, b with
| Bot k, _ | _, Bot k -> Bot k
| Implies (_, Bot _, _) , x | x, Implies (_, Bot _, _) -> x
| _ -> And(Normal, a, b) 
let disj a b = match a, b with
| Bot _, x | x , Bot _ -> x
| Implies (k, Bot k', _) , _ | _, Implies (k, Bot k', _) -> Implies (k, Bot k', Bot k')
| _ -> Or(Normal, a, b) 

let impl a b = match a, b with
| Bot _, _ -> top
| Implies (_, Bot _, _), _ -> b
| _, Implies (_, Bot _, _) -> top
| _ -> Implies(Normal, a, b) 

let same_var q = function | Var (_, q') when q = q' -> true | _ -> false

let rec list_compare c l1 l2 = match l1, l2 with
| [], [] -> 0
| [], _ :: _ -> -1
| _ :: _, [] -> 1
| h1 :: t1, h2 :: t2 -> if h1 < h2 then -1 else if h2 < h1 then 1 else list_compare c t1 t2

let vars_order q r = match q, r with |Var(_, q), Var(_, r) -> list_compare (<) q r | _ -> 0

let print_forms = List.iter (fun f -> print_string (string_of_formula f); print_string "; ")
let add_var q context =
  if List.exists (same_var q) context
  then context
  else (Var (Normal, q) :: context)

(*
  - vars : variables that have not been handled yet 
  - context : variables in the context, that already occur in the interpolant
  - imp_vars : implications variable 
  - non_invs : non-inverstible rules 
  - stack : formulas in the context that need to be handled *)
let rec e p context vars imp_vars disjs non_invs (stack : form list) : form =
  match stack with
  | [] -> (match disjs with
          | (Or(_, x, y)) :: disjs' -> (* branching E3 *)
              disj (e p context vars imp_vars disjs' non_invs [x]) (e p context vars imp_vars disjs' non_invs [y])
          | _ -> (* no more disjunctions ; need to handle invertible *)
             conj (List.fold_left (fun acc f -> if same_var p f then acc else conj acc f) top (List.sort vars_order vars)) (* E1 *)
                  (conj (List.fold_left (e8 p context [] imp_vars disjs non_invs) top non_invs)(* E8 *)
                        (List.fold_left (e4 p context [] imp_vars disjs non_invs) top imp_vars)) (* E4 *)
        ) 
  | Bot k :: _s -> Bot k;
  | And(_, x, y) :: s -> e p context vars imp_vars disjs non_invs (x :: y :: s)
  | Or (k, x, y) :: s -> e p context vars imp_vars (Or(k, x, y) :: disjs) non_invs s
  | Implies (k, Var (k', q), c) :: s ->
      if List.exists (same_var q) context
      then e p context vars imp_vars disjs non_invs (c :: s) (* E5' *)
      else e p context vars (Implies (k, Var (k', q), c) :: imp_vars) disjs non_invs s
  | Implies (_, Bot _', _) :: s -> e p context vars imp_vars disjs non_invs s (* custom *)
  | Implies(_, And(_, x, y), z) :: s ->
      e p context vars imp_vars disjs non_invs (impl x (impl y z) :: s) (* E6 *)
  | Implies(_, Or(_, x, y), z) :: s ->
      e p context vars imp_vars disjs non_invs (impl x z :: impl y z :: s) (* E7 *)
  | Implies(_, Implies(_, Bot _, _), Bot _) :: _ -> bot (* custom*)
  | Implies(k, Implies(k', x, y), z) :: s ->
      e p context vars imp_vars disjs (Implies(k, Implies(k', x, y), z) :: non_invs) s
  | Var(_, q) :: s ->
    let (imp_vars', s') = List.fold_left (try_var_mp q) ([], s) imp_vars in
        e p (add_var q context) (add_var q vars) imp_vars' disjs non_invs s'
  | Box _ :: _ | Implies(_, Box _, _) :: _ -> failwith "Modalities not handled yet" 
and e8 p context vars imp_vars disjs non_invs acc f = match f with
| Implies (_, Implies(_, x, y), z) ->
  let non_invs' = List.filter ((<>) f) non_invs in
  conj acc (impl (impl (e p context vars imp_vars disjs non_invs' [x; impl y z])
                       (a p context imp_vars disjs non_invs' [x; impl y z] y))
                 (e p context vars imp_vars disjs non_invs' [z]))
| _ -> failwith "Unexpected non-invertible rule (E8)"
and e4 p context vars imp_vars disjs non_invs acc f = match f with
| Implies (_, Var(k', q), x) when p <> q ->
  (* TODO: we made sure this never happens ; but still checking for debug*)
  (* if List.exists (same_var q) context then failwith "redundant variable E4" else is that an issue ? TODO *)
  let imp_vars' = List.filter ((<>) f) imp_vars in
  conj acc (impl (Var(k', q)) (e p (add_var q context) vars imp_vars' disjs non_invs [x]))
| Implies (_, Var(_, _), _) -> acc
| _ -> failwith "Unexpected non-invertible rule (E4)"
and a p context imp_vars disjs non_invs (stack : form list) (rhs : form) : form =
  match stack with
  | [] ->
    (match disjs with
      | Or(k, x, y) :: disjs' -> (* branching A3 *)
          conj (Implies(k, e p context [] imp_vars disjs' non_invs [x], a p context imp_vars disjs' non_invs [x] rhs))
               (Implies(k, e p context [] imp_vars disjs' non_invs [y], a p context imp_vars disjs' non_invs [y] rhs))
      | _ -> (* no more disjunctions *)
              match rhs with
              | Var (_, q) when p = q && List.exists (same_var p) context -> top (* A10  *)
              | Var (k, q) when p <> q -> Var(k, q) (* Experimental *)
              | And (_, x, y) -> conj (a p context imp_vars disjs non_invs [] x)
                                      (a p context imp_vars disjs non_invs [] y) (* A11 *)
              | Implies (_, x, y) -> impl(e p context [] imp_vars disjs non_invs [x])
                                         (a p context imp_vars disjs non_invs [x] y) (* A13 *)
              | _ ->
                disj ( disj
                        (List.fold_left (a8 p context imp_vars disjs non_invs rhs) bot non_invs)(* A8 *)
                        (List.fold_left (a4 p context imp_vars disjs non_invs rhs) bot imp_vars)) (* A4 *)
                     (match rhs with
                     | Var(k, q) when q <> p -> Var(k, q) (* A9 : Experimental : should never happen *)
                     | Or(_, x, y) -> disj (a p context imp_vars disjs non_invs [] x) (* A12 *)
                                           (a p context imp_vars disjs non_invs [] y)
                    | _ -> bot
                     )
    )
  | And(_, x, y) :: s -> a p context imp_vars disjs non_invs (x :: y :: s) rhs (* A2 *)
  | Implies (k, Var (k', q), c) :: s ->
    if List.exists (same_var q) context
    then a p context imp_vars disjs non_invs (c :: s) rhs (* A5' *)
    else a p context (Implies (k, Var (k', q), c) :: imp_vars) disjs non_invs s rhs
  | Implies (_, Bot _', _) :: s -> a p context imp_vars disjs non_invs s rhs (* custom *)
  | Implies(_, And(_, x, y), z) :: s ->
    a p context imp_vars disjs non_invs (impl x (impl y z) :: s) rhs (* E6 *)
  | Implies(_, Or(_, x, y), z) :: s ->
    a p context imp_vars disjs non_invs (impl x z :: impl y z :: s) rhs (* E7 *)
  | Implies(k, Implies(k', x, y), z) :: s ->
      a p context imp_vars disjs (Implies(k, Implies(k', x, y), z) :: non_invs) s rhs
  | Var(_, q) :: s -> if q = p && same_var p rhs then top else (* A10 *)
    let (imp_vars', s') = List.fold_left (try_var_mp q) ([], s) imp_vars in
        a p (add_var q context) imp_vars' disjs non_invs s' rhs
  | Bot _ :: s -> a p context imp_vars disjs non_invs s rhs
  | Or (k, x, y) :: s -> a p context imp_vars (Or(k, x, y) :: disjs) non_invs s rhs
  | Box _ :: _ | Implies(_, Box _, _) :: _ -> failwith "Modalities not handled yet" 
and a8 p context imp_vars disjs non_invs rhs acc f = match f with
  | Implies (_, Implies(_, x, y), z) ->
    let non_invs' = List.filter ((<>) f) non_invs in
    disj acc (conj (impl (e p context [] imp_vars disjs non_invs' [x; impl y z])
                          (a p context imp_vars disjs non_invs' [x; impl y z] y))
                  (a p context imp_vars disjs non_invs' [z] rhs))
  | _ -> failwith "Unexpected non-invertible rule (A8)"
and a4 p context imp_vars disjs non_invs rhs acc f = match f with
  | Implies (_, Var(k', q), x) when p <> q ->
    if List.exists (same_var q) context then
      a p context imp_vars disjs non_invs [x] rhs
    else
    let imp_vars' = List.filter ((<>) f) imp_vars in
    disj acc (conj (Var(k', q)) (a p (Var(k', q) :: context) imp_vars' disjs non_invs [x] rhs))
    (* TODO: could factor out q for all q → X *)
  | Implies (_, Var(_,_), _) -> acc
  | _ -> failwith "Unexpected non-invertible rule (A4)"
(* invariant : vars and imp_vars can never produce instances of ImpLVar *)
