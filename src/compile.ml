(* étiquettes
     F_function      entrée fonction
     E_function      sortie fonction
     L_xxx           sauts
     S_xxx           chaîne

   expression calculée avec la pile si besoin, résultat final dans %rdi

   fonction : arguments sur la pile, résultat dans %rax ou sur la pile

            res k
            ...
            res 1
            arg n
            ...
            arg 1
            adr. retour
   rbp ---> ancien rbp
            ...
            var locales
            ...
            calculs
   rsp ---> ...
*)

open Format
open Ast
open Tast
open X86_64

exception Anomaly of string

let debug = ref false
let strings = Hashtbl.create 32

let alloc_string =
  let r = ref 0 in
  fun s ->
    incr r;
    let l = "S_" ^ string_of_int !r in
    Hashtbl.add strings l s;
    l

let malloc n = movq (imm n) (reg rdi) ++ call "malloc"
let allocz n = movq (imm n) (reg rdi) ++ call "allocz"
let sizeof = Typing.sizeof

let new_label =
  let r = ref 0 in
  fun () ->
    incr r;
    "L_" ^ string_of_int !r

type env = {
  exit_label : string;
  mutable ofs_this : int;
  nb_locals : int ref; (* maximum *)
  mutable next_local : int; (* 0, 1, ... *)
}

let empty_env =
  { exit_label = ""; ofs_this = -1; nb_locals = ref 0; next_local = 0 }

let mk_bool d = { expr_desc = d; expr_typ = Tbool }
let mk_int i = { expr_desc = i; expr_typ = Tint }
let mk_string s = { expr_desc = s; expr_typ = Tstring }

(* f reçoit le label correspondant à ``renvoyer vrai'' *)
let compile_bool f =
  let l_true = new_label () and l_end = new_label () in
  f l_true
  ++ movq (imm 0) (reg rdi)
  ++ jmp l_end ++ label l_true
  ++ movq (imm 1) (reg rdi)
  ++ label l_end

let rec expr env e =
  match e.expr_desc with
  | TEskip -> nop
  | TEconstant (Cbool true) -> movq (imm 1) (reg rdi)
  | TEconstant (Cbool false) -> movq (imm 0) (reg rdi)
  | TEconstant (Cint x) -> movq (imm64 x) (reg rdi)
  | TEnil -> xorq (reg rdi) (reg rdi)
  | TEconstant (Cstring s) ->
      let st = alloc_string s in
      movq (lab st) (reg rdi)
  | TEbinop (Band, e1, e2) ->
      expr env (mk_bool (TEif (e1, e2, mk_bool (TEconstant (Cbool false)))))
  | TEbinop (Bor, e1, e2) ->
      expr env (mk_bool (TEif (e1, mk_bool (TEconstant (Cbool true)), e2)))
  | TEbinop (((Blt | Ble | Bgt | Bge) as op), e1, e2) ->
      expr env e1
      ++ pushq (reg rdi)
      ++ (env.ofs_this <- env.ofs_this + 8;
          expr env e2)
      ++ popq rax
      ++ (env.ofs_this <- env.ofs_this - 8;
      cmpq (reg rdi) (reg rax))
      ++ compile_bool
           (match op with
           | Blt -> jl
           | Ble -> jle
           | Bgt -> jg
           | Bge -> jge
           | _ -> assert false)
  | TEbinop (((Badd | Bsub | Bmul | Bdiv | Bmod) as op), e1, e2) -> (
      expr env e1
      ++ pushq (reg rdi)
      ++ (env.ofs_this <- env.ofs_this + 8;
      expr env e2 )++ popq rax
      ++ (env.ofs_this <- env.ofs_this - 8;
      
      match op with
      | Badd -> addq (reg rax) (reg rdi)
      | Bsub -> subq (reg rdi) (reg rax) ++ movq (reg rax) (reg rdi)
      | Bmul -> imulq (reg rax) (reg rdi)
      | Bdiv ->
          movq (imm 0) (reg rdx) ++ movq (reg rdi) (reg rsi) ++ idivq (reg rsi)
      | Bmod ->
          movq (imm 0) (reg rdx)
          ++ movq (reg rdi) (reg rsi)
          ++ idivq (reg rsi)
          ++ movq (reg rdx) (reg rax)
      | _ -> assert false))
  | TEbinop (((Beq | Bne) as op), e1, e2) ->
      expr env e1
      ++ pushq (reg rdi)
      ++ (env.ofs_this <- env.ofs_this + 8;
          expr env e2)
      ++ popq rax
      ++ (env.ofs_this <- env.ofs_this - 8;
      cmpq (reg rdi) (reg rax))
      ++ compile_bool
           (match op with Beq -> je | Bne -> jne | _ -> assert false)
  | TEunop (Uneg, e1) -> expr env e1 ++ negq (reg rdi)
  | TEunop (Unot, e1) -> expr env e1 ++ notq (reg rdi)
  | TEunop (Uamp, e1) -> (
      match e1.expr_desc with
      | TEident x -> leaq (ind ~ofs:(-x.v_addr) rbp) rdi
      | TEunop (Ustar, e) -> expr env e
      | TEdot (e, { f_ofs = ofs }) -> expr env e ++ leaq (ind ~ofs rdi) rdi
      | _ -> assert false)
  | TEunop (Ustar, e1) -> expr env e1 ++ movq (ind rdi) (reg rdi)
  | TEprint el -> (
      match el with
      | [] -> nop
      | exp :: q -> (
          match exp.expr_typ with
          | Tint | Tbool ->
              expr env exp ++ call "print_int" ++ expr env (mk_int (TEprint q))
          | Tstring ->
              expr env exp
              ++ movq (reg rdi) (reg rsi)
              ++ expr env
                   { expr_desc = TEconstant (Cstring "%s"); expr_typ = Tstring }
              ++ xorq (reg rax) (reg rax)
              ++ call "printf"
              ++ expr env (mk_string (TEprint q))
          | Tptr t -> (
              expr env exp
              ++ pushq (reg rdi)
              ++ (env.ofs_this <- env.ofs_this + 8;
               expr env)
                   { expr_desc = TEconstant (Cstring "%p"); expr_typ = Tstring }
              ++ popq rsi
              ++ (env.ofs_this <- env.ofs_this - 8;
              xorq (reg rax) (reg rax))
              ++ call "printf"
              ++
              match t with
              | Tint -> expr env (mk_int (TEprint q))
              | Tbool -> expr env (mk_bool (TEprint q))
              | Tstring -> expr env (mk_string (TEprint q))
              | _ -> assert false)
          | Tmany [] ->
              expr env
                { expr_desc = TEconstant (Cstring "(nil)"); expr_typ = Tstring }
              ++ xorq (reg rax) (reg rax)
              ++ xorq (reg rax) (reg rax)
              ++ call "printf"
          | Tmany l -> expr env exp ++ xorq (reg rax) (reg rax) ++ call "printf"
          | _ -> assert false))
  | TEident x -> movq (ind ~ofs:(-x.v_addr) rbp) (reg rdi)
  | TEassign ([ { expr_desc = TEident x } ], [ e1 ]) ->
      expr env e1 ++ movq (reg rdi) (ind ~ofs:(-x.v_addr) rbp)
  | TEassign ([ lv ], [ e1 ]) ->
      expr env e1
      ++ pushq (reg rdi)
      ++(env.ofs_this <- env.ofs_this - 8;
       expr env (mk_int (TEunop (Uamp, lv))))
      ++ popq rbx
      ++ (env.ofs_this <- env.ofs_this - 8; movq (reg rbx) (ind rdi))
  | TEassign (l, e) -> (
      match (l, e) with
      | h1 :: q1, h2 :: q2 ->
          expr env (mk_int (TEassign ([ h1 ], [ h2 ])))
          ++ expr env { expr_desc = TEassign (q1, q2); expr_typ = Tint }
      | _, _ -> nop)
  | TEblock el -> List.fold_left (fun c e -> c ++ expr env e) nop el
  | TEif (e1, e2, e3) ->
      let l1, l2 = (new_label (), new_label ()) in
      expr env e1
      ++ movq (imm 0) (reg rbx)
      ++ cmpq (reg rdi) (reg rbx)
      ++ jne l1 ++ expr env e3 ++ jmp l2 ++ label l1 ++ expr env e2 ++ label l2
  | TEfor (e1, e2) ->
      let l1, l2 = (new_label (), new_label ()) in
      label l1 ++ expr env e1
      ++ movq (imm 0) (reg rbx)
      ++ cmpq (reg rdi) (reg rbx)
      ++ je l2 ++ expr env e2 ++ jmp l1 ++ label l2
  | TEnew ty -> malloc (sizeof ty) ++ movq (reg rax) (reg rdi)
  | TEcall (f, el) ->
      let l1 = List.fold_left (push_params env) nop el in
      l1 ++ call ("F_" ^ f.fn_name) ++ addq (imm (List.length el * 8)) !%rsp
  | TEdot (e1, { f_ofs = ofs }) -> expr env e1 ++ movq (ind ~ofs rdi) (reg rdi)
  | TEvars (v1,e1) -> 
     (match e1 with
     |[]->nop
     |a::b -> (match a.expr_typ with
            |Tmany(_)-> expr env a
            |_-> expr env a ++ pushq (reg rdi)))
    let i= ref env.nb_locals in 
    match e1,i with 
        |[]-> nop
        |a::b-> popq (reg rax) ++ a.value<- (reg rax)
     

  | TEreturn [] -> jmp env.exit_label
  | TEreturn [ e1 ] -> expr env e1 ++ jmp env.exit_label
  | TEreturn _ -> assert false
  | TEincdec (e1, op) -> (
      match op with
      | Inc ->
          expr env e1
          ++ incq (reg rdi)
          ++ pushq (reg rdi)
          ++ (env.ofs_this <- env.ofs_this - 8; expr env (mk_int (TEunop (Uamp, e1))))
          ++ popq rbx
          ++(env.ofs_this <- env.ofs_this - 8; movq (reg rbx) (ind rdi))
      | Dec ->
          expr env e1
          ++ decq (reg rdi)
          ++ pushq (reg rdi)
          ++ (env.ofs_this <- env.ofs_this - 8; expr env (mk_int (TEunop (Uamp, e1))))
          ++ popq rbx
          ++ (env.ofs_this <- env.ofs_this - 8; movq (reg rbx) (ind rdi))
  )
and push_params env init e = init ++ expr env e ++ pushq (reg rdi)

let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  let ne = empty_env in
  let s = f.fn_name in
  label ("F_" ^ s)
  ++ pushq (reg rbp)
  ++ expr ne e
  ++ label ("E_" ^ s)
  ++ movq (reg rbp) (reg rsp)
  ++ popq rbp

let decl code = function
  | TDfunction (f, e) -> code ++ function_ f e
  | TDstruct _ -> code

let file ?debug:(b = false) dl =
  debug := b;
  let env = ref empty_env in
  let funs = List.fold_left decl nop dl in
  {
    text =
      globl "main" ++ label "main" ++ call "F_main"
      ++ xorq (reg rax) (reg rax)
      ++ ret ++ funs
      ++ inline
           "\n\
            print_int_or_nil:\n\
           \      test    %rdi, %rdi\n\
           \      jz      print_nil\n\
           \      movq    (%rdi), %rdi\n\
            print_int:\n\
           \      movq    %rdi, %rsi\n\
           \      movq    $S_int, %rdi\n\
           \      xorq    %rax, %rax\n\
           \      call    printf\n\
           \      ret\n\
            print_string:\n\
           \      test    %rdi, %rdi\n\
           \      jz      print_nil\n\
           \      mov     %rdi, %rsi\n\
           \      mov     $S_string, %rdi\n\
           \      xorq    %rax, %rax\n\
           \      call    printf\n\
           \      ret\n\
            print_nil:\n\
           \      mov     $S_nil, %rdi\n\
           \      xorq    %rax, %rax\n\
           \      call    printf\n\
           \      ret\n\
            print_space:\n\
           \      mov     $S_space, %rdi\n\
           \      xorq    %rax, %rax\n\
           \      call    printf\n\
           \      ret\n\n\
            print_newline:\n\
           \      mov     $S_newline, %rdi\n\
           \      xorq    %rax, %rax\n\
           \      call    printf\n\
           \      ret\n\
            print_bool:\n\
           \      xorq    %rax, %rax\n\
           \      test    %rdi, %rdi\n\
           \      jz      1f\n\
           \      mov     $S_true, %rdi\n\
           \      call    printf\n\
           \      ret\n\
            1:      mov     $S_false, %rdi\n\
           \      call    printf\n\
           \      ret\n\
            allocz:\n\
           \      movq    %rdi, %rbx\n\
           \      call    malloc\n\
           \      testq   %rbx, %rbx\n\
           \      jnz     1f\n\
           \      ret\n\
            1:    movb    $0, (%rax, %rbx)\n\
           \      decq    %rbx\n\
           \      jnz     1b\n\
           \      ret\n";
    data =
      label "S_int"
      ++ string "%ld"
      ++ label "S_string"
      ++ string "%s"
      ++ label "S_true"
      ++ string "true"
      ++ label "S_false"
      ++ string "false"
      ++ label "S_nil"
      ++ string "<nil>"
      ++ label "S_space"
      ++ string " "
      ++ label "S_newline"
      ++ string "\n"
      ++ Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop;
  }

