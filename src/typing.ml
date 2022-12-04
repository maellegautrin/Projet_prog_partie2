
open Format
open Lib
open Ast
open Tast


let debug = ref false

let dummy_loc = Lexing.dummy_pos, Lexing.dummy_pos

exception Error of Ast.location * string
exception Anomaly of string

let error loc e = raise (Error (loc, e))

(*DONE*)
type typ_struct_env = (string, structure) Hashtbl.t;;
let struct_env = Hashtbl.create 10

(*DONE*)
type func_env=(string,function_) Hashtbl.t;;
let fonction_env = Hashtbl.create 10

let typ_function = ref []

let rec debug_type = function
 | Tint -> print_string "int\n"
 | Tbool -> print_string "bool\n"
 | Tstring -> print_string "string\n"
 | Tmany [] -> print_string "tvoid\n"
 | Tptr t -> print_string "pointeur"; debug_type t
 | Tmany (h::q) -> debug_type h; debug_type (Tmany q)
 | Tstruct s -> print_string s.s_name; print_string "\n"

let debug_expr = function
| TEskip -> print_string "skip\n"
| TEconstant _ -> print_string "constante\n"
| TEbinop _ -> print_string "binop\n"
| TEunop _ -> print_string "unop\n"
| TEnil -> print_string "vide\n"
| TEnew _ -> print_string "new\n"
| TEcall _ -> print_string "appel fonction\n"
| TEident _ -> print_string "variable\n"
| TEdot _ -> print_string "champ structure\n"
| TEassign _ -> print_string "assignation\n"
| TEvars _ -> print_string "decl variable\n"
| TEif _ -> print_string "if\n"
| TEreturn _ -> print_string "return\n"
| TEblock _ -> print_string "block\n"
| TEfor _ -> print_string "boucle for\n"
| TEprint _ -> print_string "print\n"
| TEincdec _ -> print_string "incr/decr\n"

let create_list length var =
  let rec aux length var l = match length with 
    | 0 -> l
    | _ -> aux (length - 1) var (var::l)
  in aux length var []

let rec type_type loc = function
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTident { id } when Hashtbl.mem struct_env id -> Tstruct(Hashtbl.find struct_env id)
  | PTptr ty -> Tptr (type_type loc ty)
  | _ -> raise (Error (loc, "type inconnu")) 

let rec eq_type ty1 ty2 = match ty1, ty2 with
  | Tint, Tint 
  | Tbool, Tbool
  | Tstring, Tstring -> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | Tmany [], Tmany [] -> true
  | Tmany (t1::q1), Tmany (t2::q2) -> (eq_type t1 t2) && (eq_type (Tmany q1) (Tmany q2))
  | _,_ -> false
    (* DONE *)


let fmt_used = ref false
let fmt_imported = ref false

let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let new_var =
  let id = ref 0 in
  fun x loc ?(used=false) ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty; v_used = used; v_addr = 0; v_depth = 0 } 
let id_var_entry_bloc = ref 0
module Env = struct
  module M = Map.Make(String)
  type t = var M.t
  let empty = M.empty
  let find = M.find
  let add env v = M.add v.v_name v env

  let all_vars = ref []
  let check_unused () =
    let check v =
      if v.v_name <> "_" && v.v_used = false then error v.v_loc "variable inutilisee" in
    List.iter check !all_vars

  let var x loc ?used ty env =
    let v = new_var x loc ?used ty in
    all_vars := v :: !all_vars;
    add env v, v

  (* TODO type () et vecteur de types *)
end

let env_f = ref Env.empty
let tvoid = Tmany [];;
let make d ty = { expr_desc = d; expr_typ = ty }
let stmt d = make d tvoid

let rec expr env e =
 let e, ty, rt = expr_desc env e.pexpr_loc e.pexpr_desc in
  { expr_desc = e; expr_typ = ty }, rt

and expr_desc env loc = function
  | PEskip ->TEskip, tvoid, false
  | PEconstant c -> ( match c with
                        | Cbool _ -> TEconstant c, Tbool, false
                        | Cint _ ->  TEconstant c, Tint, false
                        | Cstring _ -> TEconstant c, Tstring, false
                    )
  | PEbinop (op, e1, e2) -> let exp1,rt1 = expr env e1 and exp2,rt2 = expr env e2 in
                         ( if not(eq_type exp1.expr_typ exp2.expr_typ) then raise (Error (loc,"type inconnu")) 
                           else match op with 
                            | Badd 
                            | Bsub 
                            | Bmul 
                            | Bdiv 
                            | Bmod 
                            | Blt 
                            | Ble 
                            | Bgt 
                            | Bge when not(eq_type exp1.expr_typ Tint) -> error loc ("incompatibilite")
                            | Band 
                            | Bor when not(eq_type exp1.expr_typ Tbool) -> error loc ("incompatibilite")
                            | Beq 
                            | Bne -> ( match exp1.expr_desc,exp2.expr_desc with 
                                        | TEnil,TEnil -> error loc ("expressions vides")
                                        | _ ->  TEbinop (op, exp1, exp2),Tbool,false
                                      )
                           | Blt 
                           | Ble 
                           | Bgt 
                           | Bge -> TEbinop (op, exp1, exp2),Tbool,false
                           | _ -> TEbinop (op, exp1, exp2),exp1.expr_typ,false
      )
  | PEunop (Uamp, e1) -> ( let exp,rt = expr env e1 in 
                          is_l_value loc exp;
                          TEunop (Uamp, exp), Tptr exp.expr_typ, false 
                          )
  | PEunop (Uneg, e1) -> ( let exp,rt = expr env e1 in
                          if eq_type exp.expr_typ Tint then TEunop (Uneg, exp), Tint, false
                          else error loc "int attendu"
                          )
  | PEunop (Unot, e1) -> ( let exp,rt = expr env e1 in
                            if eq_type exp.expr_typ Tbool then TEunop (Uneg, exp), Tbool, false
                            else error loc "bool attendu"
                          )
  | PEunop (Ustar, e1) ->( let exp,rt = expr env e1 in 
                          match exp.expr_desc, exp.expr_typ with
                               | TEnil, _ -> error loc "expression vide"
                               | _, Tptr t -> TEunop (Ustar, exp), t, false
                               | _ -> error loc "pointeur attendu"
                          )
  | PEcall ({id = "fmt.Print"}, el) -> fmt_used := true; 
                                      let tel = List.map (pexpr_to_expr env) el in TEprint tel, tvoid, false
  | PEcall ({id="new"}, [{pexpr_desc=PEident {id}}]) -> let ty = match id with
                                                          | "int" -> Tint 
                                                          | "bool" -> Tbool 
                                                          | "string" -> Tstring
                                                          | _ when Hashtbl.mem struct_env id -> Tstruct (Hashtbl.find struct_env id) 
                                                          | _ -> error loc ("mauvais type") in
                                                                 TEnew ty, Tptr ty, false
  | PEcall ({id="new"}, _) ->  error loc "pas de type"
  | PEcall (id, el) -> ( if not(Hashtbl.mem fonction_env id.id) then error loc "fonction inconnue"
                        else (let l_entry = List.map (pexpr_to_expr env) el and f,exp = (Hashtbl.find fonction_env id.id) in 
                               if f.fn_params = [] && l_entry <> [] then error loc "pas d'argument pour cette fonction"
                              else match l_entry with
                                    | [{expr_desc=TEcall (g,l_entry_g)}] when compare_typ_var f.fn_params g.fn_typ -> if List.length f.fn_typ = 1 then TEcall (f,l_entry), List.hd (f.fn_typ), false
                                                                                                                      else TEcall (f,l_entry), Tmany f.fn_typ, false
                                    | l when compare_typ_var f.fn_params (ltyp_of_exp l) -> if List.length f.fn_typ = 1 then TEcall (f,l_entry), List.hd (f.fn_typ), false
                                                                                            else TEcall (f,l_entry), Tmany f.fn_typ, false
                                    | _ -> error loc "mauvais type"
                             )
                        )
  | PEfor (e, b) ->( let e1,rt1 = expr env e and e2,rt2 = expr env b in
                    if not(eq_type e1.expr_typ Tbool) then error loc "bool attendu"
                    else TEfor (e1,e2), tvoid, false
                    )
  | PEif (e1, e2, e3) -> let exp1,rt1 = expr env e1
                          and exp2,rt2 = expr env e2
                          and exp3,rt3 = expr env e3 in
                        if eq_type exp1.expr_typ Tbool then 
                         TEif (exp1,exp2,exp3),tvoid,rt2&&rt3
                        else error loc "bool attendu"
  | PEnil -> TEnil, tvoid, false
  | PEident {id=id} -> if id = "_" then error loc "mauvais appel"
                      else ( try let v = Env.find id !env_f in 
                            v.v_used <- true;
                            TEident v, v.v_typ, false
                            with Not_found -> error loc ("variable inconnue")
                            )
  | PEdot (e, id) ->( let exp,rt = expr env e in
                      match exp.expr_typ with
                          | Tstruct s 
                          | Tptr Tstruct s when exp.expr_desc <> TEnil -> let fields = s.s_fields in 
                              if not(Hashtbl.mem fields id.id) then error loc "inconnu"
                              else let f = Hashtbl.find fields id.id in TEdot (exp, f), f.f_typ, false
                          | _ -> error loc "pas une structure"
                     )
  | PEassign (lvl, el) -> ( let rec aux = function
                             | [] -> []
                             | {pexpr_desc = PEident {id=id}; pexpr_loc}::t ->  (try 
                                                                                let v = Env.find id !env_f in
                                                                                {expr_desc = TEident v;expr_typ = v.v_typ}::aux t
                                                                                with Not_found -> error pexpr_loc ("variable inconnue")) 
                             | h::t -> (fst (expr env h))::(aux t)
                            in 
                            let el1 = aux lvl and el2 = List.map (pexpr_to_expr env) el in
                           (List.iter (is_l_value loc) el1; List.iter (if_tvoid_then_nil loc) el2;
                            let ltyp2 = ltyp_of_exp el2 in
                             match el2 with
                                  | [{expr_desc=TEcall (f,l);expr_typ}] when compare_typ_assign el1 f.fn_typ -> TEassign (el1,el2), tvoid, false
                                  | l when compare_typ_assign el1 ltyp2 -> TEassign (el1,el2), tvoid, false
                                  | _ -> error loc "mauvais type"
                             )
                           )
  | PEreturn el -> (let l = List.map (pexpr_to_expr env) el in
                   let ltyp = ltyp_of_exp l in
                     match l with 
                          | [{expr_desc=TEcall (f,l_return);expr_typ}] when (eq_type (Tmany (!typ_function)) expr_typ) -> TEreturn l, tvoid, true
                          | l when compare_typ ltyp !typ_function -> TEreturn l, tvoid, true
                          | _ -> error loc "mauvais type de retour"
                    )
  | PEblock el -> let old_env = !env_f and old_entry_var = !id_var_entry_bloc in
                  ( id_var_entry_bloc := !id_var;
                  let l = List.map (traitement_block env) el in 
                  let l = List.flatten l in
                  (*List.iter (fun (e,b) -> debug_expr e.expr_desc) l;*)
                  let l_expr, rt = list_block l in
                  env_f := old_env; id_var_entry_bloc := old_entry_var;
                  TEblock l_expr, tvoid, rt
                  )
  | PEincdec (e, op) ->( let exp,rt = expr env e in 
                        ( is_l_value loc exp;
                        if eq_type exp.expr_typ Tint then TEincdec (exp,op), Tint, true else error loc "mauvais type"
                         )
                       )
  | PEvars (il,ty,pl) ->( let tl = List.map (pexpr_to_expr env) pl and pil = List.map (fun x -> {pexpr_desc=PEident x;pexpr_loc=loc}) il in 
                          let pe2 = {pexpr_desc=PEassign (pil,pl);pexpr_loc = loc} in
                          match ty with
                            | None ->( match tl with
                                      | [] -> error loc "mauvais type"
                                      | [{expr_desc=TEcall (f,params)}] -> let lvar = add_var_typ il f.fn_typ loc in 
                                                                          let e1 = {expr_desc=TEvars lvar; expr_typ=tvoid} and e2,rt2 = expr env pe2 in
                                                                           TEblock [e1;e2], tvoid, false
                                      | _ -> List.iter (non_empty loc) tl; 
                                             let tyl = ltyp_of_exp tl in 
                                             let lvar = add_var_typ il tyl loc in 
                                             let e1 = {expr_desc=TEvars lvar; expr_typ=tvoid} and e2,rt2 = expr env pe2 in
                                             TEblock [e1;e2], tvoid, false
                                      )
                            | Some typ -> ( let t = type_type loc typ in 
                                            let ltyp = create_list (List.length il) t in
                                            match tl with
                                               | [] -> let lvar = add_var_typ il ltyp loc in TEvars lvar, tvoid, false
                                               | [{expr_desc=TEcall (f,params)}] -> if compare_typ ltyp f.fn_typ then 
                                                                                     ( let lvar = add_var_typ il ltyp loc in 
                                                                                       let e1 = {expr_desc=TEvars lvar; expr_typ=tvoid} and e2,rt2 = expr env pe2 in
                                                                                       TEblock [e1;e2], tvoid, false
                                                                                      )
                                                                                    else error loc "mauvais types"
                                                 | _ ->  let tyl = ltyp_of_exp tl in 
                                                         if compare_typ ltyp tyl then 
                                                              ( let lvar = add_var_typ il ltyp loc in 
                                                               let e1 = {expr_desc=TEvars lvar; expr_typ=tvoid} and e2,rt2 = expr env pe2 in
                                                               TEblock [e1;e2], tvoid, false
                                                               )
                                                       else error loc "mauvais types"
                                           )
                        )
and traitement_block env e = match e with
    | {pexpr_desc = PEvars _} -> 
      let exp,b = expr env e in 
        (
        match exp with 
          |{expr_desc=TEblock [e1;e2]}-> [(e1,b);(e2,b)]
          | _ -> [(exp,b)]
        )
    | _ -> [expr env e]
                  
and pexpr_to_expr env e = 
  let exp,rt = expr env e in exp

and list_block = function
  | [] -> [],false
  | (e,rt)::q -> let l,rt_block = list_block q in e::l,(rt || rt_block)

and ltyp_of_exp = function
    | [] -> []
    | {expr_typ}::q -> expr_typ::(ltyp_of_exp q)

and compare_typ l1 l2 = match l1,l2 with
    | [],[] -> true
    | (Tptr t)::q1,(Tmany [])::q2 -> compare_typ q1 q2 
    | t1::q1,t2::q2 when (eq_type t1 t2) -> compare_typ q1 q2
    | _ -> false

and compare_typ_var lvar lparam = match lvar,lparam with
    | [],[] -> true
    | {v_typ=t1}::q1,t2::q2 when eq_type t1 t2 -> compare_typ_var q1 q2
    | _,_ -> false

and compare_typ_assign el ltyp = match el,ltyp with
    | [],[] -> true
    | {expr_typ=Tptr t}::q1,(Tmany [])::q2 -> compare_typ_assign q1 q2
    | {expr_desc=TEident v}::q1,t::q2 when v.v_name = "_" -> compare_typ_assign q1 q2
    | {expr_typ=t1}::q1,t2::q2 when (eq_type t1 t2) -> compare_typ_assign q1 q2
    | _,_ -> false
    
and add_var_typ li lt loc_act = match li,lt with
    | [],[] -> []
    | {loc;id}::q1,t::q2 -> 
        (
        try let v = Env.find id !env_f in 
          if v.v_id > !id_var_entry_bloc && id <> "_" then error loc_act "variable trop utilisees"
          else (let env,v = Env.var id loc t !env_f in (env_f := env; v::(add_var_typ q1 q2 loc_act)))
        with Not_found -> let env,v = Env.var id loc t !env_f in (env_f := env; v::(add_var_typ q1 q2 loc_act))
        )
    | _,_ -> error loc_act "trop de variables"

and non_empty loc = function
    | {expr_desc=TEnil} -> error loc "expression vide"
    | _ -> ()

and is_l_value loc = function
    | {expr_desc=TEident v} -> ()
    | {expr_desc=TEdot (v,f)} -> is_l_value loc v
    | {expr_desc=TEunop (Ustar,v)} -> ()
    | _ -> error loc "l-value attendue"

and if_tvoid_then_nil loc = function
    | {expr_desc=TEnil} -> ()
    | {expr_typ= Tmany []} -> error loc " expression de type"
    | _ -> ()

let found_main = ref false

(* 1. declare structures *)

let phase1 = function
  | PDstruct { ps_name = { id ; loc }; ps_fields} -> 
      (
        if Hashtbl.mem struct_env id then raise (Error (loc,"struct utilisee plusieurs fois"))
        else add struct_env id { s_name = id; s_fields = (create 1)} 
      )
  | PDfunction _ -> ()

let rec sizeof = function
  | Tint 
  | Tbool 
  | Tstring 
  | Tptr _ -> 8
  | Tstruct s -> Hashtbl.fold sizeof_fields (s.s_fields) 0
  | Tmany l -> List.fold_left (fun init x -> (sizeof x) + init) 0 l
and sizeof_fields key field init = 
  (sizeof (field.f_typ)) + init

(* 2. declare functions and type fields *)

let to_tfield l_field struct_fields = 
  let rec aux size_ofs = function
    | [] -> ()
    | ({id;loc},typ)::q -> if Hashtbl.mem struct_fields id then raise (Error (loc, "utilises plusieurs fois"))
                            else 
                            let typ = type_type loc typ in
                            let ofs = sizeof typ
                            in
                            add struct_fields id {f_name = id;f_typ = typ;f_ofs = size_ofs}; aux (size_ofs + ofs) q 
  in aux 0 l_field 

let rec to_tparam = function
  | [] -> []
  | ({loc;id},typ)::q -> (new_var id loc (type_type loc typ))::(to_tparam q)
  
let rec to_ttyp loc = function
  | [] -> []
  | h::q -> (type_type loc h)::(to_ttyp loc q)

let rec is_param_used l_param name = match l_param with
  | [] -> false
  | {v_name}::q when v_name = name -> true
  | h::q -> is_param_used q name 

let rec is_param_dist = function
  | [] -> true
  | {v_name}::q -> if is_param_used q v_name then false else is_param_dist q

let phase2 = function
  | PDfunction { pf_name={id; loc} ; pf_params=pl; pf_typ=tyl; pf_body} ->
      (if id = "main" then 
          (found_main := true; if pl <> [] then error loc "trop d'argument"; if tyl <> [] then error loc "trop d'argument");
        if Hashtbl.mem fonction_env id then raise (Error (loc,"plusieur fonction aux même nom"))
        else let new_pl = to_tparam pl and new_typ = to_ttyp loc tyl in
          let f = {fn_name = id; fn_params = (new_pl); fn_typ = new_typ} in
            add fonction_env id (f,pf_body);
          if not(is_param_dist new_pl) then raise (Error (loc,"plusieur parametre avec le même nom"))
      )
  | PDstruct { ps_name = {id;loc}; ps_fields = fl } -> let fields = (Hashtbl.find struct_env id).s_fields in to_tfield fl fields

(* 3. type check function bodies *)

let is_lvar_in  l = 
  let rec aux env = function
    | [] -> env
    | v::q -> aux (Env.add env v) q
  in aux Env.empty l

let is_recursive_structure loc s lvu = 
  let rec etude_fields fields lvu =
    Hashtbl.iter (aux lvu) fields
  and aux lvu key f =
    match f.f_typ with
      | Tstruct sf -> if List.(Hashtbl.mem) sf.s_name lvu then (error loc "structure recursive")
                      else etude_fields sf.s_fields (sf.s_name::lvu)
      | _ -> ()
  in etude_fields s.s_fields lvu

let decl = function
  | PDfunction { pf_name={id; loc}; pf_body = e; pf_typ=tyl; pf_params=pl } ->
    (
      typ_function := ptyp_to_ttyp loc tyl;
      let f,exp = Hashtbl.find fonction_env id in
          env_f := (is_lvar_in  f.fn_params);
          env_f := Env.add (!env_f) (new_var "_" dummy_loc tvoid);
          let e, rt = expr !env_f e in 
            if rt = false && f.fn_typ <> [] then error loc "type unit"
            else let f,exp = Hashtbl.find fonction_env id in TDfunction (f, e)
    )
  | PDstruct {ps_name={id;loc}} ->
    let s = Hashtbl.find struct_env id in
     (is_recursive_structure loc s [s.s_name]; TDstruct s) 
     
let file ~debug:b (imp, dl) =
  debug := b;
  (* fmt_imported := imp; *)
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "missing method main";
  let dl = List.map decl dl in
  Env.check_unused (); 
  if imp && not !fmt_used then error dummy_loc "fmt imported but not used";
  if not(imp) && !fmt_used then error dummy_loc "fmt used but not imported";
  dl
