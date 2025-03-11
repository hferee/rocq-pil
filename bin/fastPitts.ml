open PIL.Formulas
open PIL.Extraction

let top = Implies(Normal, Bot Normal, Bot Normal)
let bot = Bot Normal


(* tries to apply modus ponens for a variable and place the variable in the relevant stack *)
let try_var_mp q (impVs, stack) f = match f with
  | Implies(_, Var(_, q'), f') when q = q' ->
      (impVs, f' :: stack)
  | _ -> (f :: impVs, stack)

  (* TODO : have new and old vars *)

let conj a b = And(Normal, a, b) 
let disj a b = Or(Normal, a, b) 

let same_var q = function | Var (_, q') when q = q' -> true | _ -> false

let rec e p vars impVs disjs nInv (stack : form list) : form =
  match stack with
  | [] -> (match disjs with
          | (Or(_, x, y)) :: disjs' -> (* branching E3 *)
              disj (e p vars impVs disjs' nInv [x]) (e p vars impVs disjs' nInv [y])
          | _ -> (* no more disjunctions ; need to handle invertible *)
             conj (List.fold_left (fun acc f -> if same_var p f then acc else conj acc f) top vars) (* E1 *)
                  (conj (List.fold_left (e8 p vars impVs disjs nInv) top nInv)(* E8 *)
                        (List.fold_left (e4 p vars impVs disjs nInv) top impVs)) (* E4 *)
        ) 
  | Bot k :: _s -> Bot k;
  | And(_, x, y) :: s -> e p vars impVs disjs nInv (x :: y :: s)
  | Or (k, x, y) :: s -> e p vars impVs (Or(k, x, y) :: disjs) nInv s
  | Implies (k, Var (k', q), c) :: s ->
      if List.exists (same_var q) vars 
      then e p vars impVs disjs nInv (c :: s) (* E5' *)
      else e p vars (Implies (k, Var (k', q), c) :: impVs) disjs nInv s
  | Implies (_, Bot _', _) :: s -> e p vars impVs disjs nInv s (* custom *)
  | Implies(k', And(k, x, y), z) :: s ->
      e p vars impVs disjs nInv (Implies(k', x, Implies(k, y, z)) :: s) (* E6 *)
  | Implies(k, Or(_, x, y), z) :: s ->
      e p vars impVs disjs nInv (Implies(k, x, z) :: Implies(k, y, z) :: s) (* E7 *)
  | Implies(k, Implies(k', x, y), z) :: s ->
      e p vars impVs disjs (Implies(k, Implies(k', x, y), z) :: nInv) s
  | Var(k, q) :: s ->
    let (impVs', s') = List.fold_left (try_var_mp q) ([], s) impVs in
        e p (Var(k, q) :: vars) impVs' disjs nInv s'
  | Box _ :: _ | Implies(_, Box _, _) :: _ -> failwith "Modalities not handled yet" 
and e8 p vars impVs disjs nInv acc f = match f with
| Implies (k, Implies(k', x, y), z) ->
  let nInv' = List.filter ((<>) f) nInv in
  conj acc (Implies (k, Implies(k', e p vars impVs disjs nInv' [x; Implies(k', y, z)],
                                    a p vars impVs disjs nInv' [x; Implies(k', y, z)] y),
                        e p vars impVs disjs nInv' [z]))
| _ -> failwith "Unexpected non-invertible rule (E8)"
and e4 p vars impVs disjs nInv acc f = match f with
| Implies (k, Var(k', q), x) when p <> q ->
  let impVs' = List.filter ((<>) f) impVs in
  conj acc (Implies (k, Var(k', q), e p vars impVs' disjs nInv [x]))
| Implies (_, Var(_, _), _) -> acc
| _ -> failwith "Unexpected non-invertible rule (E4)"
and a p vars impVs disjs nInv (stack : form list) (rhs : form) : form =
  match stack with
  | [] ->
    (match disjs with
      | Or(k, x, y) :: disjs' -> (* branching A3 *)
          disj (Implies(k, e p vars impVs disjs' nInv [x], a p vars impVs disjs' nInv [x] rhs))
               (Implies(k, e p vars impVs disjs' nInv [y], a p vars impVs disjs' nInv [y] rhs))
      | _ -> (* no more disjunctions *)
              match rhs with
              | Var (_, q) when p = q && List.exists (same_var p) vars -> top (* A10  *)
              | And (k, x, y) -> And(k, a p vars impVs disjs nInv [] x,
                                        a p vars impVs disjs nInv [] y) (* A11 *)
              | Implies (k, x, y) -> Implies(k, e p vars impVs disjs nInv [x],
                                                a p vars impVs disjs nInv [x] y) (* A13 *)
              | _ ->
                disj ( disj
                        (List.fold_left (a8 p vars impVs disjs nInv rhs) bot nInv)(* A8 *)
                        (List.fold_left (a4 p vars impVs disjs nInv rhs) bot impVs)) (* A4 *)
                     (match rhs with
                     | Var(k, q) when q <> p -> Var(k, q) (* A9 *)
                     | Or(k, x, y) -> Or(k, a p vars impVs disjs nInv [] x, (* A12 *)
                                            a p vars impVs disjs nInv [] y)
                    | _ -> bot
                     )
    )
  | And(_, x, y) :: s -> a p vars impVs disjs nInv (x :: y :: s) rhs (* A2 *)
  | Implies (k, Var (k', q), c) :: s ->
    if List.exists (same_var q) vars
    then a p vars impVs disjs nInv (c :: s) rhs (* A5' *)
    else a p vars (Implies (k, Var (k', q), c) :: impVs) disjs nInv s rhs
  | Implies (_, Bot _', _) :: s -> a p vars impVs disjs nInv s rhs (* custom *)
  | Implies(k', And(k, x, y), z) :: s ->
    a p vars impVs disjs nInv (Implies(k', x, Implies(k, y, z)) :: s) rhs (* E6 *)
  | Implies(k, Or(_, x, y), z) :: s ->
    a p vars impVs disjs nInv (Implies(k, x, z) :: Implies(k, y, z) :: s) rhs (* E7 *)
  | Implies(k, Implies(k', x, y), z) :: s ->
      a p vars impVs disjs (Implies(k, Implies(k', x, y), z) :: nInv) s rhs
  | Var(k, q) :: s -> if q = p && same_var p rhs then top else (* A10 *)
    let (impVs', s') = List.fold_left (try_var_mp q) ([], s) impVs in
        a p (Var(k, q) :: vars) impVs' disjs nInv s' rhs
  | Bot _ :: s -> a p vars impVs disjs nInv s rhs
  | Or (k, x, y) :: s -> a p vars impVs (Or(k, x, y) :: disjs) nInv s rhs
  | Box _ :: _ | Implies(_, Box _, _) :: _ -> failwith "Modalities not handled yet" 
and a8 p vars impVs disjs nInv rhs acc f = match f with
  | Implies (k, Implies(k', x, y), z) ->
    let nInv' = List.filter ((<>) f) nInv in
    disj acc (And (k, Implies(k', e p vars impVs disjs nInv' [x; Implies(k', y, z)],
                                  a p vars impVs disjs nInv' [x; Implies(k', y, z)] y),
                          a p vars impVs disjs nInv' [z] rhs))
  | _ -> failwith "Unexpected non-invertible rule (A8)"
and a4 p vars impVs disjs nInv rhs acc f = match f with
  | Implies (k, Var(k', q), x) when p <> q ->
    let impVs' = List.filter ((<>) f) impVs in
    disj acc (And (k, Var(k', q), a p vars impVs' disjs nInv [x] rhs))
    (* TODO: could factor out q for all q → X *)
  | Implies (_, Var(_,_), _) -> acc
  | _ -> failwith "Unexpected non-invertible rule (A4)"
(* invariant : vars and impVs can never produce instances of ImpLVar *)

(* todo actually use p! -> check E *)