
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
type struct_env = (string, structure) Hashtbl.t;;
let struct_v = Hashtbl.create(30);;

(*DONE*)
type func_env=(string,function_) Hashtbl.t;;
let funct_v= Hashtbl.create(30);;

let rec type_type = function
  | PTident { id = "int" } -> Tint
  | PTident { id = "bool" } -> Tbool
  | PTident { id = "string" } -> Tstring
  | PTptr ty -> Tptr (type_type ty)
  | PTident {id= a;loc=l}-> match (Hashtbl.find_opt struct_v a) with
                    | None -> error l ("unknown struct")
                    | Some(x) -> Tstruct (x)
;;


let rec eq_type ty1 ty2 = match ty1, ty2 with
  | Tint, Tint 
  | Tbool, Tbool 
  | Tstring, Tstring -> true
  | Tstruct s1, Tstruct s2 -> s1 == s2
  | Tptr ty1, Tptr ty2 -> eq_type ty1 ty2
  | _ -> false
    (*TO DO*)

let fmt_used = ref false
let fmt_imported = ref false

let evar v = { expr_desc = TEident v; expr_typ = v.v_typ }

let new_var =
  let id = ref 0 in
  fun x loc ?(used=false) ty ->
    incr id;
    { v_name = x; v_id = !id; v_loc = loc; v_typ = ty; v_used = used; v_addr = 0; v_depth = 0 } 

module Env = struct
  module M = Map.Make(String)
  type t = var M.t
  let empty = M.empty
  let find = M.find
  let add env v = M.add v.v_name v env

  let all_vars = ref []
  let check_unused () =
    let check v =
      if v.v_name <> "_" && not v.v_used then error v.v_loc "unused variable" in(*DONE*)
    List.iter check !all_vars


  let var x loc ?used ty env =
    let v = new_var x loc ?used ty in
    all_vars := v :: !all_vars;
    add env v, v

  (* TODO type () et vecteur de types *)
end

let tvoid = Tmany []
let make d ty = { expr_desc = d; expr_typ = ty }
let stmt d = make d tvoid

let rec expr env e =
 let e, ty, rt = expr_desc env e.pexpr_loc e.pexpr_desc in
  { expr_desc = e; expr_typ = ty }, rt

and expr_desc env loc = function
  | PEskip ->
     TEskip, tvoid, false
  | PEconstant c ->(
    match c with 
      |Cbool(a)_->TEconstant(a),Tbool,false
      |Cint(a)->TEconstant(a),Tint,false
      |Cstring(a)->TEconstant(a),Tstring,false)
  | PEbinop (op, e1, e2) ->(
    let f1 = expr env e1 in
    let f2= expr env e2 in
    (match op with
      | Badd 
      | Bsub
      | Bmul 
      | Bdiv 
      | Bmod -> if f1.expr_typ <> Tint || f2.expr_typ <> Tint then errtyp loc Tint f1.expr_typ;
                TEbinop(op,fst te1, fst te2), Tint,false
      | Beq 
      | Bne ->  if f1.expr_desc = TEnil && f2.expr_desc = TEnil then error loc "";
                TEbinop(op,f1,f2),Tbool,false
      | Blt
      | Ble 
      | Bgt 
      | Bge -> if f1.expr_typ <> Tint  then errtyp loc Tint f1.expr_typ;
                                 if f2.expr_typ <> Tint  then errtyp loc Tint f2.expr_typ;
                                 TEbinop(op,f1, f2), Tbool,false
      | Band 
      | Bor -> if f1.expr_typ <> Tbool then errtyp loc Tbool f1.expr_typ;
               if f2.expr_typ <> Tbool then errtyp loc Tbool f2.expr_typ;
               TEbinop(op,f1, f2), Tbool,false)
       )
  | PEunop (Uamp, e) -> if islvalue e.pexpr_desc then let f = expr env e in TEunop (Uamp, fst f), Tptr ((fst f).expr_typ), false
                        else error loc ("pas l-value")
  | PEunop (Uneg, e1) -> let f = expr env e1 in
                         if (fst f).expr_typ = Tint then TEunop (Uneg, fst f), Tint, false
                         else error loc ("not int")
  | PEunop (Uneg | Unot | Ustar as op, e1) -> let f = fst (expr env e1) in
                                              (match f.expr_typ with
                                                |Tint -> if op <> Uneg then error e1.pexpr_loc "int" ;TEunop(op,f),f.expr_typ,false
                                                |Tbool -> if op <> Unot then error e1.pexpr_loc "bool" ;
                                                          TEunop(op,f),f.expr_typ,false
                                                |Tptr(a) -> if op <> Ustar then error e1.pexpr_loc "ptr";
                                                            TEunop(op,f),a,false
                                                |_ -> error e1.pexpr_loc "mauvais type")
  | PEcall ({id = "fmt.Print"}, el) -> (if not !fmt_imported then error loc ("import fmt"););
                                       fmt_used := true;
                                       let f = List.map (exprx env) el in
                                       TEprint f, tvoid, false
  | PEcall ({id="new"}, [{pexpr_desc=PEident {id}}]) -> let ty = match id with
                                                          | "int" -> Tint
                                                          | "bool" -> Tbool
                                                          | "string" -> Tstring
                                                          | _ -> 
                                                      if Hashtbl.mem tablestructs id then type_type (PTident {id ; loc})
                                                      else error loc ("type inconnu ")
                                                      in TEnew ty, Tptr ty, false
   | PEcall ({id="new"}, _) -> error loc "pas de type"
   | PEcall (id, el) -> (
                         try
                         let pf = Funcs.find id.id in
                         let el_typee = List.map (exprx env) el in
                         let f = {fn_name = pf.pf_name.id ; fn_typ = List.map type_type pf.pf_typ ;
                         fn_params = List.map (fun (id,typ) -> new_var id.id id.loc (type_type typ)) pf.pf_params} in
                         let typ = listtotype f.fn_typ in
                         TEcall(f,el_typee), typ , false
                         with |Not_found -> error loc ("inconnue")
                         )
    | PEfor (e, b) -> let ptb = expr env e in
                      (if (snd ptb) then error loc ("booléen avec return"););
                       if (fst ptb).expr_typ = Tbool then
                            let f = expr env b in TEfor f, tvoid, snd f
                       else error loc ("type bool attendu dans test de for")
    | PEif (e1, e2, e3) -> let f1 = expr env e1 in
                           let f2 = expr env e2 in 
                           let f3 = expr env e3 in
                           (if (snd f1) then error loc ("booléen avec return"););
                           if (fst f1).expr_typ = Tbool then TEif (fst f1,fst ff2, fst f3), tvoid, (snd f2) && (snd f3)
                           else error loc ("pas de bool")
    | PEnil -> TEnil, tvoid, false
    | PEident {id=id}-> (
                         try 
                         let v = Env.find id !envactuel in v.v_used <- true;
                         TEident v, v.v_typ, false
                         with Not_found -> error loc ("variable non référencée)
                         )
     | PEdot (e, id) ->(
                       let f = exprx env e in
                       match f.expr_typ with
                          |Tstruct a 
                          |Tptr (Tstruct a) ->(
                                               try
                                               let s = Hashtbl.find tablestructs a.s_name in
                                               if Hashtbl.mem s.s_fields id.id then 
                                                     let field = Hashtbl.find s.s_fields id.id in
                                                     TEdot(newe,field),field.f_typ,false
                                               else error loc ("la structure"^s.s_name^"n'a pas de champ"^id.id)
                                               with 
                                              |Not_found -> error loc ("structure inconnue")
                                                   )
                          | _ -> error loc ("struct inconnue")
                         )
      
       | PEassign (lvl, el) -> if List.for_all (fun x -> islvalue x.pexpr_desc) lvl then
                                    let nlvl = List.length lvl and nel = List.length el in
                                    (
                                    if nlvl < nel then error loc ("trop de r-values")
                                    else if nlvl > nel then error loc ("trop de l-values")
                                    );
                               let newlvl = List.map (exprx env) lvl in
                               let newel = List.map (exprx env) el in
                               validassign newlvl newel loc;
                               TEassign (newlvl, newel), tvoid, false 
                               else error loc "l-value attendue pour assignation"
        | PEreturn el -> let t1 = List.map (exprx env) el in
                         let ret = listtotype (List.map (fun x -> x.expr_typ) t1) in
                         if retour = !typederetour then TEreturn t1, tvoid, true
                         else error loc "mauvais type de retour"
        | PEblock el ->let t1 = List.map (exprx env) el in
                       let r = List.exists (r env) el in
                       TEblock t1, tvoid, r
        | PEincdec (e, op) -> let (f,_,_) = expr_desc env loc e.pexpr_desc in
                              if tyx = Tint then TEincdec (make dx tyx, op), Tint, false
                              else error loc ("pas de int")
        | PEvars (il, ty, el) -> let t1 = List.map (exprx env) el in
                                     match ty with
                                      |None -> (
                                                   match el_typee with
                                                     | [] -> error loc ("expression")
                                                     | [{expr_desc = TEcall (f,params)}] -> let listevars = nv_var_type il f.fn_typ loc in TEvars listevars, tvoid, false
                                                     |_ ->List.iter (fun x -> if x.expr_desc = TEnil then error loc "expression vide dans assign") el_typee;
                                                          let typelist = typeofexprlist el_typee in
                                                          let listevars = nv_var_type il typelist loc in TEvars listevars, tvoid, false
                                                 )
                                      |Some typev ->(
                                                     let t = type_type typev in
                                                     let ltypes = List.init (List.length il) (fun n -> t) in
                                                     match t1 with
                                                         |[] -> let listevars = nv_var_type il ltypes loc in TEvars listevars, tvoid, false
                                                         |[{expr_desc = TEcall (f,params)}] -> if eqlist eq_type ltypes f.fn_typ then (let listevars = nv_var_type il ltypes loc in TEvars listevars, tvoid, false)
                                                                                               else error loc "types incompatibles"
                                                         | _ -> let typelist = typeofexprlist el_typee in
                                                                if eqlist eq_typeLR ltypes typelist then (let listevars = nv_var_type il ltypes loc in TEvars listevars, tvoid, false)
                                                                else error loc "incompatible"
                                                     )

let found_main = ref false

(* 1. declare structures *)
let phase1 = function
  | PDstruct { ps_name = { id = id; loc = loc }} -> (* TODO *) ()
  | PDfunction _ -> ()

let sizeof = function
  | Tint 
  | Tbool 
  | Tstring 
  | Tptr _ -> 8
  | _ -> (* TODO *) assert false 

(* 2. declare functions and type fields *)
let phase2 = function
  | PDfunction ({ pf_name={id; loc}; pf_params=pl; pf_typ=tyl; } as f) -> if id="main" then (
                                                                          if pl <> [] then error loc "trop d'arguments";
                                                                          if tyl <> [] then error loc "return";
                                                                          found_main := true);
                                                                          if List.for_all is_well_formed (List.map snd pl) && List.for_all is_well_formed tyl then 
                                                                          Funcs.add f
                                                                          else error loc ("fonction "^id^" is ill-formed")
  | PDstruct { ps_name = {id}; ps_fields = fl } -> if not (List.for_all is_well_formed (List.map snd fl)) then error loc id;
                                                   if not (Pstructs.are_fields_unique s) then error loc ("duplicate attributes in structure "^s.ps_name.id);
                                                   Pstructs.add s

(* 3. type check function bodies *)
let decl = function
  | PDfunction { pf_name={id; loc}; pf_body = e; pf_typ=tyl } -> let return_type = List.map type_type tyl in
                                                                 ret_type := l_to_typ return_type;
                                                                 let params = ref [] in
                                                                 let env = ref Env.new_env in
                                                                 List.iter (fun (p,t) -> let (a,b) = (Env.var p.id p.loc (type_type t) !env) in
                                                                 env := a;params := b::!params) pfparams ;
                                                                 let f = { fn_name = id; fn_params = []; fn_typ = []} in
                                                                 let e, rt = expr Env.empty e in
                                                                 TDfunction (f, e)
  | PDstruct {ps_name={id}} ->
    (* TODO *) let s = { s_name = id; s_fields = Hashtbl.create 5; s_size = 0 } in
     TDstruct s

let file ~debug:b (imp, dl) =
  debug := b;
  (* fmt_imported := imp; *)
  List.iter phase1 dl;
  List.iter phase2 dl;
  if not !found_main then error dummy_loc "missing method main";
  let dl = List.map decl dl in
  Env.check_unused (); (* TODO variables non utilisees *)
  if imp && not !fmt_used then error dummy_loc "fmt imported but not used";
  dl
