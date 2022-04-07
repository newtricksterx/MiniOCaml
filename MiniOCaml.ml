(* TODO: Write a good set of tests for unused_vars. *)
let unused_vars_tests = [
  (Let ("x", I 1, I 5), ["x"]); 
  (Rec ("x", Int, I 5), ["x"]);
  (Rec ("x", Int, Primop(Plus, [Var "x" ; I 5])), []);
  (Fn ([("x", Int); ("y", Int)],
       Primop (Plus,
               [Primop (Times, [Var "x"; Var "x"]);
                Primop (Times, [I 5; I 5])])) , ["y"]);
  (Fn ([("x", Int); ("y", Int)],
       Primop (Plus,
               [Primop (Times, [Var "x"; Var "x"]);
                Primop (Times, [Var "y"; Var "y"])])) , []);
  
  (Apply (ex1, [ex2;ex3]), [])
]

(* TODO: Implement the missing cases of unused_vars. *)
let rec unused_vars =
  function
  | Var _ | I _ | B _ -> []
  | If (e, e1, e2) -> unused_vars e @ unused_vars e1 @ unused_vars e2
  | Primop (_, args) ->
      List.fold_left (fun acc exp -> acc @ unused_vars exp) [] args
  | Let (x, e1, e2) ->
      let unused = unused_vars e1 @ unused_vars e2 in
      if List.mem x (free_variables e2) then
        unused
      else
        x :: unused

  | Rec (x, _, e) -> 
      let unused = unused_vars e in
      if (List.mem x (free_variables e)) then
        unused
      else 
        x :: unused

  | Fn (xs, e) -> 
      let unused = unused_vars e in
      let rec check_all_names xs l =
        match xs with
        |[] -> l
        |(x, _)::t -> 
            if(List.mem x (free_variables e)) then
              check_all_names t l
            else 
              check_all_names t (x::l)
      in check_all_names xs unused
        
  | Apply (e, es) -> 
      let unused = unused_vars e in 
      let rec check_all_exp es l = 
        match es with
        |[] -> l
        |e1::t -> check_all_exp t (unused_vars e1 @ l) 
      in check_all_exp es unused

(* TODO: Write a good set of tests for subst. *)
let subst_tests : (((exp * name) * exp) * exp) list = [
  (((I 1, "x"), (* [1/x] *)
    (* let y = 2 in y + x *)
    Let ("y", I 2, Primop(Plus, [Var "y" ; Var "x"]))),
   (* let y = 2 in y + 1 *)
   Let ("y", I 2, Primop(Plus, [Var "y"; I 1])));
  
  (((I 1, "x"), 
    Rec ("y", Int, Primop (Plus, [Var "y"; Var "x"]))),
     
   Rec("y", Int, Primop (Plus, [Var "y"; I 1]))
  );
  
  
  (((Primop(Plus, [Var "x"; Var "y"]), "x"), 
    Rec ("y", Int, Primop (Plus, [Var "y"; Var "x"]))),
     
   Rec("y'", Int, Primop (Plus, [Var "y'"; Primop(Plus, [Var "x"; Var "y"])]))
  );
  
  (((Primop(Plus, [I 1; I 2]), "y"), 
    Rec ("y", Int, Primop (Plus, [Var "y"; Var "x"]))),
     
   Rec("y", Int, Primop (Plus, [Var "y"; Var "x"]))
  );
  
  
  (((Primop(Plus, [I 1; Var "y"]), "x"), 
    Fn ([("y", Int)], Primop (Plus, [Var "y"; Var "x"]))),
     
   Fn ([("y'", Int)], Primop (Plus, [Var "y'"; Primop(Plus, [I 1; Var "y"])]))
  );
  
  (((Primop(Plus, [I 1; Var "y"]), "x"), 
    Fn ([("y", Int);("z", Int)], Primop (Plus, [Var "z"; Var "x"]))),
     
   Fn ([("y'", Int);("z'", Int)], Primop (Plus, [Var "z'"; Primop(Plus, [I 1; Var "y"])]))
  );
  
  (((I 1, "y"), 
    Fn ([("y", Int)], Primop (Plus, [I 2; Var "x"]))),
     
   Fn ([("y", Int)], Primop (Plus, [I 2; Var "x"]))
  );
  
  (((I 1, "y"), 
    Fn ([("y", Int)], Primop (Plus, [Var "y"; Var "x"]))),
     
   Fn ([("y", Int)], Primop (Plus, [Var "y"; Var "x"]))
  );
  
  (((I 1, "x"), 
    Fn ([("y", Int)], Primop (Plus, [Var "t"; Var "x"]))),
     
   Fn ([("y", Int)], Primop (Plus, [Var "t"; I 1]))
  );
  
  (((I 1, "x"), 
    Fn ([("x", Int)], Primop (Plus, [Var "t"; Var "x"]))),
     
   Fn ([("x", Int)], Primop (Plus, [Var "t"; Var "x"]))
  );
  
  (((I 1, "x"), 
    Fn ([("z", Int); ("y", Arrow([Int], Int))], Var "x")),
     
   Fn ([("z", Int);("y", Arrow([Int], Int))], I 1)
  );
  
  (((Var "y", "x"), 
    Fn ([("y", Int);("z", Int)], Primop (Plus, [Var "t"; Var "x"]))),
     
   Fn ([("y'", Int);("z'", Int)], Primop (Plus, [Var "t"; Var "y"]))
  );
  
  (((Primop(Plus, [(Var "t");(Var "y")]), "x"), 
    Fn ([("y", Int);("z", Int)], Primop (Plus, [Var "t"; Var "x"]))),
     
   Fn ([("y'", Int);("z'", Int)], Primop (Plus, [Var "t"; Primop(Plus, [(Var "t");(Var "y")])]))
  );
  
  (((I 1, "x"), 
    Apply(Var "y",[ (Primop (Plus, [Var "y"; Var "x"])); Var "x" ] )),
     
   Apply(Var "y", [ (Primop (Plus, [Var "y"; I 1])); I 1])
  );
  
  (((Primop(Plus, [I 1; Var "y"]), "x"), 
    Apply(Var "y",[ (Primop (Plus, [Var "y"; Var "x"])); Var "x" ] )),
     
   Apply(Var "y",[ (Primop (Plus, [Var "y"; Primop(Plus, [I 1; Var "y"])])); Primop(Plus, [I 1; Var "y"]) ] )
  );
  
  (*
    (((I 1, "x"), 
      Fn ([("y", Int)], Primop (Plus, [Var "y"; Var "x"]))),
     
     Fn ([("y", Int)], Primop (Plus, [Var "y"; I 1]))
    );
  
    *)
  
]

let rec check_all_names1 xs x =
  match xs with
  |[] -> false
  |(y, _)::t -> 
      if(y = x) then true
      else check_all_names1 t x
          
let rec check_all_names2 xs e' = 
  match xs with
  |[] -> false
  |(y, _)::t ->
      if (List.mem y (free_variables e')) then true
      else check_all_names2 t e'
          
let rec get_names_list xs acc =
  match xs with
  |[] -> acc
  |(n, _)::t -> get_names_list t (n::acc) 
          
let rec get_names r_list xs acc e =
  match (r_list, xs) with 
  |( (n::t1, e), (_, tp)::t2 ) -> get_names (t1, e) t2 ((n, tp)::acc) e
  |(_, _) -> (acc, e)
  

(* TODO: Implement the missing cases of subst. *)
let rec subst ((e', x) as s) exp =
  match exp with
  | Var y ->
      if x = y then e'
      else Var y
  | I n -> I n
  | B b -> B b
  | Primop (po, args) -> Primop (po, List.map (subst s) args)
  | If (e, e1, e2) ->
      If (subst s e, subst s e1, subst s e2)
  | Let (y, e1, e2) ->
      let e1' = subst s e1 in
      if y = x then
        Let (y, e1', e2)
      else
        let (y, e2) =
          if List.mem y (free_variables e') then
            rename y e2
          else
            (y, e2)
        in
        Let (y, e1', subst s e2)

  | Rec (y, t, e) -> 
      if(y = x) then 
        Rec (y, t, e)
      else
        let (y, e) = 
          if List.mem y (free_variables e') then
            rename y e
          else 
            (y, e)
        in 
        Rec (y, t, subst s e)
  

  | Fn (xs, e) -> 
      if (check_all_names1 xs x) then Fn (xs, e)
      else 
        let (xs, e) = 
          get_names (rename_all ((get_names_list xs [])) e) (List.rev(xs)) [] e
        in
        Fn ((xs), subst s e)
      
      (*
        if (check_all_names1 xs x) then Fn (xs, e)
        else 
          let (xs, e) = 
            if(check_all_names2 xs e') then 
              get_names (rename_all ((get_names_list xs [])) e) xs [] e
            else
              (xs, e)
          in 
          Fn (xs, subst s e)
      *)
  
  | Apply (e, es) -> 
      Apply(subst s e, List.map (subst s) es) 
        
and rename x e =
  let x' = freshVar x in
  (x', subst (Var x', x) e)

and rename_all names exp =
  List.fold_right
    (fun name (names, exp) ->
       let (name', exp') = rename name exp in
       (name' :: names, exp'))
    names
    ([], exp)

(* Applying a list of substitutions to an expression, leftmost first *)
let subst_list subs exp =
  List.fold_left (fun exp sub -> subst sub exp) exp subs


(* TODO: Write a good set of tests for eval. *)
let eval_tests = [

  (Let ("x", I 1, Primop (Plus, [Var "x"; I 5])), I 6); 
  (Rec ("x", Int, Primop(Plus, [I 6; I 2])), I 8); 
  (Rec ("y", Bool, B true), B true); 
  (Rec ("x", Int, Let ("y", I 1, Primop (Plus, [Var "y"; I 5]))), I 6);
  
  (Apply (Fn ([("x", Int)], Var "x"), [(I 6)]), I 6); 
  (Apply (Fn ([("x", Bool);("x", Int)], Var "x"), [(B true);(I 2)]), B true);
  (Apply (Fn ([("x", Int); ("y", Int)], Var "x"), [(I 6);(I 7)]), I 6);
  (Apply (Fn ([("x", Int);("y", Int)], Primop(Plus, [Var "x"; Var "y"])), [(I 6);(I 1)]), I 7);
  (Apply (Fn ([("x", Int)], Fn ([("y", Int)], Var "y")), [(I 6)]), Fn ([("y", Int)], Var "y")); 
  (Apply (Fn ([], I 6), []), I 6);
  (Apply (Fn ([("x", Int)], Primop(Plus, [(Var "x");(I 2)])), [(I 2)]), I 4);
  (Apply (Fn ([("x", Int)], Fn([("y", Int)], Var "y")), [(I 2)]), Fn([("y", Int)], Var "y")); 
  (Apply (Fn ([("x", Arrow([Int], Int))], I 6), [I 6]), I 6); 
  (Apply (Fn ([("x", Int)], Var "x"), [I 2]), I 2);
  (Apply (Fn ([("y", Bool)], Var "y"), [I 2]), I 2);

  (Apply (Fn ([], Let ("x", I 1, Primop (Plus, [Var "x"; I 5]))), []), I 6);
  (Apply (Fn ([("x", Int)], I 1),[I 15]), I 1);
  (Apply (Fn ([("x", Arrow([Int], Int))], Var "x"), [I 6]), I 6); 
  (Apply (Fn ([("x", Arrow([Int], Int));("y", Bool)], Var "y"), [I 6; B false]), B false);
  (Apply (If(B true, Fn ([], I 6),  I 2), []), I 6); 
]

(* TODO: Implement the missing cases of eval. *)
let rec eval exp =
  match exp with
  (* Values evaluate to themselves *)
  | I _ -> exp
  | B _ -> exp
  | Fn _ -> exp

  (* This evaluator is _not_ environment-based. Variables should never
     appear during evaluation since they should be substituted away when
     eliminating binding constructs, e.g. function applications and lets.
     Therefore, if we encounter a variable, we raise an error.
*)
  | Var x -> raise (Stuck (Free_variable x))

  (* Primitive operations: +, -, *, <, = *)
  | Primop (po, args) ->
      let args = List.map eval args in
      begin
        match eval_op po args with
        | None -> raise (Stuck Bad_primop_args)
        | Some v -> v
      end

  | If (e, e1, e2) ->
      begin
        match eval e with
        | B true -> eval e1
        | B false -> eval e2
        | _ -> raise (Stuck If_non_true_false)
      end

  | Let (x, e1, e2) ->
      let e1 = eval e1 in
      eval (subst (e1, x) e2)
        
  | Rec (f, _, e) -> 
      let e' = eval e 
      in 
      if(List.mem f (free_variables e)) then
        eval (subst (exp ,f) e')
      else 
        e'
               
      
      (*
        let e' = eval e 
        in
        eval (subst (e, f) e') 
    *)    
  | Apply (e, es) -> 
      begin
        match e with
        | Fn (nl, e') -> 
            if (List.length(nl) = List.length(es)) then
              eval (subst_list (List.combine es (List.rev(get_names_list nl []))) e')
            else
              raise (Stuck Arity_mismatch)
        | _ -> 
            begin
              match eval e with
              |Fn (nl, e') -> 
                  if (List.length(nl) = List.length(es)) then
                    eval (subst_list (List.combine es (List.rev(get_names_list nl []))) e')
                  else
                    raise (Stuck Arity_mismatch)
              | _ -> raise (Stuck Apply_non_fn)
            end
            
      end

(* TODO: Write a good set of tests for infer. *)
let infer_tests = [
  (* An example test case.
     Note that you are *only* required to write tests for Rec, Fn, and Apply!
  *)
  (([("x", Int)], Var "x"), Int);
  (([], Rec("y", Int, Var "y")), Int); 
  
  (([("x", Int)], Fn([("x", Int)], I 6)), Arrow([Int], Int));
  (([("y", Int)], Fn([("x", Int)], I 6)), Arrow([Int], Int));
  (([("x", Int);("y", Int)], Fn([("x", Int);("y", Int)], I 6)), Arrow([Int; Int], Int));
  (([("z", Int);("t", Int)], Fn([("x", Int);("y", Int)], Var "x")), Arrow([Int; Int], Int));
  (([("z", Int);("t", Bool);("i", Int)], Fn([("y", Int)], Var "y")), Arrow([Int], Int));
  (([], Fn([], I 6)), Arrow([], Int));
  
  (([("x",Int)], Apply(Fn ([("x", Int)], Var "x"),[I 2])), Int);
  (([("x", Int); ("y", Int)], Apply(Fn ([("x", Int);("y", Int)], Var "x"),[I 2; I 3])), Int);
  (([], Apply(Fn ([], I 1),[])), Int);
  
  (([("r", Arrow ([Bool; Bool], Int))],
    (Apply (Var "r", [B false; B false]))), Int)
]
let rec extract_tp xs acc = 
  match xs with
  |[] -> acc
  |(_, tp)::t -> extract_tp t (acc @ [tp])
                   
let rec get_tp xs x =
  match xs with
  |(n, tp)::t -> 
      if(n = x) then tp
      else get_tp t x
  |_ -> Int
(* TODO: Implement the missing cases of infer. *)
let rec infer ctx e =
  match e with
  | Var x ->
      begin
        try lookup x ctx
        with Not_found -> raise (TypeError (Free_variable x))
      end
  | I _ -> Int
  | B _ -> Bool

  | Primop (po, exps) ->
      let (domain, range) = primopType po in
      check ctx exps domain range

  | If (e, e1, e2) ->
      begin
        match infer ctx e with
        | Bool ->
            let t1 = infer ctx e1 in
            let t2 = infer ctx e2 in
            if t1 = t2 then t1
            else type_mismatch t1 t2
        | t -> type_mismatch Bool t
      end

  | Let (x, e1, e2) ->
      let t1 = infer ctx e1 in
      infer (extend ctx (x, t1)) e2

  | Rec (f, t, e) ->
      begin
        match e with
        |I _ -> 
            if(t = Int) then Int
            else raise (TypeError(Type_mismatch(t, Int)))
        |B _ ->             
            if(t = Bool) then Bool
            else raise (TypeError(Type_mismatch(t, Bool)))
        |Var v -> 
            if(f = v) then t
            else raise (TypeError(Free_variable v))
        |_ -> 
            let inferred = infer (extend ctx (f, t)) e in
            if (List.mem f (free_variables e)) then
              if(inferred = t) then inferred
              else raise (TypeError(Type_mismatch(t, inferred)))
            else
              inferred
      end 

  | Fn (xs, e) -> 
      begin
        match e with
        |I _ -> Arrow(extract_tp xs [], Int)
        |B _ -> Arrow(extract_tp xs [], Bool)
        |Var v -> Arrow(extract_tp xs [], get_tp xs v)
        |_ -> Arrow(extract_tp xs [], infer (extend_list ctx xs) e)
      end 
                    
  | Apply (e, es) -> 
      match infer ctx e with 
      |Arrow(xs, y) ->
          begin
            let rec suitable xs es =
              match (xs, es) with
              |(t'::t1, e::es) ->
                  if(t' = infer ctx e) then
                    suitable t1 es
                  else 
                    type_mismatch t' (infer ctx e)
              |([], _::_) -> raise (TypeError(Arity_mismatch))
              |(_::_, []) -> raise (TypeError(Arity_mismatch))
              |_ -> y
            in suitable xs es
          end
          
          
      |t' -> raise (TypeError (Apply_non_arrow t'))
      (*
        match infer ctx e with 
        |Arrow([], x) -> x
        |Arrow(xs, y) -> 
            begin 
              let rec s xs es = 
                match (xs, es) with
                |(t'::t1, e::t2) -> 
                    if (t' = (infer ctx e)) then
                      s t1 t2
                    else (type_mismatch t' (infer ctx e))
                |([], _::_) -> raise (TypeError(Arity_mismatch))
                |(_::_, []) -> raise (TypeError(Arity_mismatch))
                |_ -> Arrow(xs, y)
              in s xs es 
            end
        |t' -> raise (TypeError (Apply_non_arrow t'))
               
      *)
      (*
        let rec all_tp_in_es es acc =
          match es with
          |[] -> acc
          |e::t -> all_tp_in_es t (acc @ [(infer ctx e)])
        in 
        Arrow(all_tp_in_es es [], infer ctx e)
      
      *)

and check ctx exps tps result =
  match exps, tps with
  | [], [] -> result
  | e :: es, t :: ts ->
      let t' = infer ctx e in
      if t = t' then check ctx es ts result
      else type_mismatch t t'
  | _ -> raise (TypeError Arity_mismatch)

           
(* TODO: Implement type unification. *)
let rec unify (t1 : utp) (t2 : utp) : unit =
  match t1, t2 with
  (* unifying identical concrete types does nothing *)
  | UInt, UInt
  | UBool, UBool -> ()
  (* For type constructors, recursively unify the parts *)
  | UArrow (t1, t1'), UArrow (t2, t2') ->
      (unify t1 t2; unify t1' t2')
  | UTVar a, _ -> unifyVar a t2
  | _, UTVar b -> unifyVar b t1
  (* All other cases are mismatched types. *)
  | _, _ -> unif_error @@ UnifMismatch (t1, t2) 
        
(* Unify a variable with a type *)
and unifyVar a t = 
  match a with
  |{contents = None} -> 
      begin
        match t with
        |(UTVar b) -> 
            begin 
              match b with
              |{contents = None} -> 
                  if (a = b) then ()
                  else a := Some (UTVar b)
              |{contents = Some s} -> unify (UTVar(a)) s
            end
        |_ -> 
            if(occurs a t) then unif_error UnifOccursCheckFails
            else a := Some t
      end
  |{contents = Some n} -> unify n t
                      
                            