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

let rec insert_list x = function
  | [] -> []
  | [e] -> [e]
  | h::t -> h::x::(insert_list x t)

let malloc n = movq (imm n) (reg rdi) ++ call "malloc"
let allocz n = movq (imm n) (reg rdi) ++ call "allocz"

let sizeof = Typing.sizeof

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r

type env = {
  exit_label: string;
  mutable ofs_this: int;
  mutable nb_locals: int; (* maximum *)
  mutable next_local: int; (* 0, 1, ... *)
}
let empty_env =
  { exit_label = ""; ofs_this = -1; nb_locals = 0; next_local = 0 }

let fun_env f =
  { empty_env with exit_label = "E_" ^ f.fn_name; nb_locals= 0}

  let mk_bool d = { expr_desc = d; expr_typ = Tbool } (*crée une expression expr à partir d'une expr_desc de type bool*)
  let mk_int i = { expr_desc = i; expr_typ = Tint } (*crée une expression expr à partir d'une expr_desc de type int*)
  let mk_string s = { expr_desc = s; expr_typ = Tstring } (*crée une expression expr à partir d'une expr_desc de type string*)

(* f reçoit le label correspondant à ``renvoyer vrai'' *)
let compile_bool f =
  let l_true = new_label () and l_end = new_label () in
  f l_true
  ++ movq (imm 0) (reg rdi)
  ++ jmp l_end ++ label l_true
  ++ movq (imm 1) (reg rdi)
  ++ label l_end

let rec expr ?(copy=false) env e = match e.expr_desc with
| TEskip -> nop (* on écrit rien dans le .s*)
| TEconstant (Cbool true) -> movq (imm 1) (reg rdi) (* on place la constante qui est un booléen dans rdi *)
| TEconstant (Cbool false) -> movq (imm 0) (reg rdi) (*idem*)
| TEconstant (Cint x) -> movq (imm64 x) (reg rdi)(*idem pour un entier*)
| TEnil -> xorq (reg rdi) (reg rdi)
| TEconstant (Cstring s) -> (*pour une string il faut d'abord allouer de la mémoire grâce à alloc_string puis stocker dans rdi *)
    let st = alloc_string s in
    leaq (lab st) rdi
| TEbinop (Band, e1, e2) -> (* pour le "et" lazy, on utilise le if pour vérifier que la première condition est vraie avant de tester la deuxième*)
    expr env (mk_bool (TEif (e1, e2, mk_bool (TEconstant (Cbool false)))))
| TEbinop (Bor, e1, e2) ->(*même chose que pour le et*)
    expr env (mk_bool (TEif (e1, mk_bool (TEconstant (Cbool true)), e2)))
| TEbinop (((Blt | Ble | Bgt | Bge) as op), e1, e2) ->
    expr env e1
    ++ pushq (reg rdi)
    ++ (env.ofs_this <- env.ofs_this + 8; (* on met à jour le ofs_this car on a ajouté sur la pile*)
        expr env e2)
    ++ popq rax
    ++ (env.ofs_this <- env.ofs_this - 8; (*idem*)
    cmpq (reg rdi) (reg rax)) (* on effectue la comparaison puis on appel compile_bool avec le drapeau correspondant à l'opérateur*)
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
    
    match op with (* on distingue les cas de manière classique*)
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
         (match op with  (*appel de compile_bool pour mettre à vrai ou faux en fonction du drapeau calculé par cmpq*)
         Beq -> je 
         | Bne -> jne 
         | _ -> assert false)
| TEunop (Uneg, e1) -> expr env e1 ++ negq (reg rdi)
| TEunop (Unot, e1) -> expr env e1 ++ notq (reg rdi)
| TEunop (Uamp, e1) -> ( (*il faut ici aller rechercher l'addresse ce qui se fait gr^ce à l'opérateur leaq*)
    match e1.expr_desc with
    | TEident x -> leaq (ind ~ofs:(x.v_addr) rbp) rdi
    | TEunop (Ustar, e) -> expr env e (* ce cas est évident car il on de mande l'addresse de la valeur à une addresse *)
    | TEdot (e, { f_ofs = ofs }) -> expr env e ++ leaq (ind ~ofs rdi) rdi
    | _ -> assert false)
| TEunop (Ustar, e1) -> expr env e1 ++ movq (ind rdi) (reg rdi)
| TEprint el -> ( (*on regarde la liste d'expression à afficher*)
    match el with
    | [] -> nop
    | exp :: q -> ( (* on afficher expression par expression*)
        match exp.expr_typ with (* il faut donc crée un label pour afficher chaque type ce qui est fait plus bas*)
        | Tint | Tbool -> (* pour un int ou un bool, il suffit juste d'appeler "print_int"*)
            expr env exp ++ call "print_int" ++ expr env (mk_int (TEprint q))
        | Tstring ->
            expr env exp
            ++ movq (reg rdi) (reg rsi)
            ++ expr env
                 { expr_desc = TEconstant (Cstring "%s"); expr_typ = Tstring } (* il faut aussi évaluer l'expression avec %s pour les arguments de type string*)
            ++ xorq (reg rax) (reg rax)
            ++ call "printf" (*appel de printf qui est déja dans x86_64*)
            ++ expr env (mk_string (TEprint q)) (*on print le reste de la liste*)
        | Tptr t -> (
            expr env exp
            ++ pushq (reg rdi)
            ++ (env.ofs_this <- env.ofs_this + 8;
             expr env)
                 { expr_desc = TEconstant (Cstring "%p"); expr_typ = Tstring } (*idem*)
            ++ popq rsi
            ++ (env.ofs_this <- env.ofs_this - 8;
            xorq (reg rax) (reg rax))
            ++ call "printf" (*pour le %p*)
            ++
            match t with (*on recommence l'affichage avec le type de l'objet pointé*)
            | Tint -> expr env (mk_int (TEprint q))
            | Tbool -> expr env (mk_bool (TEprint q))
            | Tstring -> expr env (mk_string (TEprint q))
            | _ -> assert false)
        | Tmany [] ->
            expr env
              { expr_desc = TEconstant (Cstring "(nil)"); expr_typ = Tstring }(* pour le Tmany sans arguments on affiche nil*)
            ++ xorq (reg rax) (reg rax)
            ++ xorq (reg rax) (reg rax)
            ++ call "printf"
        | Tmany l -> expr env exp ++ xorq (reg rax) (reg rax) ++ call "printf"  (*sinon, il s'agit juste d'un printf habituel*)
        | _ -> let print_call exp = match exp.expr_typ with
        | Tint -> call "print_int"
        | Tbool -> call "print_bool"
        | Tstring -> call "print_string"
        | Tptr _ -> call "print_ptr"
        | Tstruct s -> call ("print_struct_"^s.s_name)
        | _ -> nop
      in 
      let rec gen_as = function
        | [] -> nop
        | [e1] -> expr env e1 ++ print_call e1
        | e1::e2::t ->
          if e1.expr_typ = Tstring || e2.expr_typ = Tstring then expr env e1 ++ print_call e1 ++ gen_as (e2::t)
          else expr env e1 ++ print_call e1 ++ call "print_space" ++ gen_as (e2::t)
      in
      gen_as el))
  | TEident x -> (match x.v_typ with
      | Tstruct s when copy ->
        movq (imm s.s_size) (reg rdi) ++
        call "allocz" ++
        begin
          match e.expr_desc with
            | TEident x ->
           (match e.expr_typ with
              | Tstruct _ -> movq (ind rbp ~ofs:x.v_addr) (reg rdi)
              | _ -> movq (reg rbp) (reg rdi) ++ addq (imm x.v_addr) (reg rdi)
            )
           | TEunop (Ustar, e) -> expr env e
           | TEdot (e,x) ->  expr env e ++
             addq (imm x.f_ofs) (reg rdi)
           | _ -> assert false (* ce n'est pas une l-value *)
        end ++
      
       pushq (reg rbx) ++
       movq (reg rax) (reg rbx) ++
       movq (reg rax) (reg rsi) ++
       movq (imm s.s_size) (reg rdx) ++
       call "copy_struct" ++ (* copy_struct doesn't use %rbx *)
        movq (reg rbx) (reg rdi) ++
       popq rbx
     | _ -> movq (ind ~ofs:x.v_addr rbp) (reg rdi))
  | TEassign ([v1], [e1]) -> expr env e1
  ++ pushq (reg rdi)
  ++(env.ofs_this <- env.ofs_this - 8; (* mise à jour du ofs_this*)
   expr env (mk_int (TEunop (Uamp, v1))))
  ++ popq rbx
  ++ (env.ofs_this <- env.ofs_this - 8; movq (reg rbx) (ind rdi))
  | TEassign (l, e) -> (
      match (l, e) with
      | h1 :: q1, h2 :: q2 ->
          expr env (mk_int (TEassign ([ h1 ], [ h2 ])))
          ++ expr env { expr_desc = TEassign (q1, q2); expr_typ = Tint }
      | _, _ -> nop)
  | TEblock el -> 
    let rec eval_block env = function
      | [] -> nop
      | {expr_desc= TEvars (vl, el)}::t -> begin 
       let i = ref ((-8) * (env.nb_locals + 1)) in (* on retient l'addresse de la pile où est stocké la valeur de la variable à assigner*)
       let rec assignation_liste l= match l with
        |[]->()
        |a::b->  a.v_addr <- !i; i := !i-8; assignation_liste b 
       in assignation_liste vl;
         env.nb_locals <- env.nb_locals + (List.length vl);
         (if el = [] then 
        let rec iter_valeur l=match l with
         |[]-> nop
         |a::b-> begin match a.v_typ with
            | Tstruct s ->
              movq (imm s.s_size) (reg rdi) ++
              call "allocz" ++
               movq (reg rax) (reg rdi)
            | _ -> xorq (reg rdi) (reg rdi)
            end
            ++ pushq (reg rdi) ++ iter_valeur b
           
        in 
         iter_valeur vl
         else
          let rec iter_val l=match l with
         |[]-> nop
         |a::b-> expr env a ~copy:true ++
         (match a.expr_typ with
           | Tmany _ -> nop
           | _ -> pushq (reg rdi)) ++ iter_val b
         in iter_val el ++ eval_block env t)
        end 
        | h::t -> expr env h ++ eval_block env t (*on effectue récursievement l'évaluation expression par expression parmi les la liste dans le block*) 
 in eval_block env el
  | TEif (e1, e2, e3) ->
      let l1, l2 = (new_label (), new_label ()) in  (*on crée ici un label pour le "then" et pour le "else"*)
      expr env e1
      ++ movq (imm 0) (reg rbx)
      ++ cmpq (reg rdi) (reg rbx) 
      ++ jne l1 ++ expr env e3 ++ jmp l2 ++ label l1 ++ expr env e2 ++ label l2 (*on appel de else ou le then en fonction de la valeur de e1*)
  | TEfor (e1, e2) ->
      let l1, l2 = (new_label (), new_label ()) in
      label l1 ++ expr env e1
      ++ movq (imm 0) (reg rbx)
      ++ cmpq (reg rdi) (reg rbx)(* on compare le résultat de e1 avec false*)
      ++ je l2 ++ expr env e2 ++ jmp l1 ++ label l2 (* si e1 alors on va à l2 avec je et l2 renvoi à l1 pour recommencer le test*)
  | TEnew ty -> malloc (sizeof ty) ++ movq (reg rax) (reg rdi) (* on alloue de la place de la bonne taille puis on stocke*)
  | TEcall (f, el) ->
      let l1 = List.fold_left (push_params env) nop el in (* évaluation des parametres*)
      l1 ++ call ("F_" ^ f.fn_name) ++ addq (imm (List.length el * 8)) !%rsp (*appel de la fonction avec les arguments stockés sur la pile*)
  | TEdot (e1, { f_ofs = ofs }) -> expr env e1 ++ movq (ind ~ofs rdi) (reg rdi)
  | TEvars _ ->
     assert false (* fait dans block *)
 | TEreturn [] -> jmp env.exit_label (* on appel le label de retour qui est stocké dans la mémoire du label*)
 | TEreturn [ e1 ] -> expr env e1 ++ jmp env.exit_label
 | TEreturn _ -> assert false
 | TEincdec (e1, op) -> (
         match op with (* on distngue les cas incrémentation ét décrémentation*)
         | Inc ->
             expr env e1
             ++ incq (reg rdi) (*on évalue les parametres et on les met sur la pile*)
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

and addresse env e = match e.expr_desc with
  | TEident x ->
    (match e.expr_typ with
      | Tstruct _ -> movq (ind rbp ~ofs:x.v_addr) (reg rdi)
      | _ -> movq (reg rbp) (reg rdi) ++ addq (imm x.v_addr) (reg rdi))
  | TEunop (Ustar, e) ->
    expr env e
  | TEdot (e,x) ->
    expr env e ++
    addq (imm x.f_ofs) (reg rdi)
  | _ -> assert false (* ce n'est pas une l-value *)

let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  let s = f.fn_name in
  let env = fun_env f in
  let args_addr = ref ((List.length f.fn_params) * 8 + 8) in
  List.iter (fun v -> v.v_addr <- !args_addr; args_addr := !args_addr - 8) f.fn_params;
    label ("F_" ^ s) ++
    pushq (reg rbp) ++
    movq (reg rsp) (reg rbp) ++
    expr env e ++
    label ("E_" ^ s) ++
    movq (reg rbp) (reg rsp) ++
    popq rbp ++
    (if List.length f.fn_typ > 1 then
      popq r15 ++ (
      let c = ref nop in
      for i = 1 to ((List.length f.fn_typ)*8 / 8) do
      c := !c ++ pushq (ind rsp ~ofs:(-8 - 16))
      done;
      !c)
    ++
      pushq (reg r15)
    else nop) ++
    ret

let decl code = function
  | TDfunction (f, e) -> code ++ function_ f e
  | TDstruct _ -> code
let allocz =
  let loop_lab = new_label () in
    label "allocz" ++
      pushq (reg rbx) ++
      movq (reg rdi) (reg rbx) ++
      call "malloc" ++
    label loop_lab ++
      decq (reg rbx) ++
      movb (imm 0) (ind rax ~index:rbx) ++
      testq (reg rbx) (reg rbx) ++
      jnz loop_lab ++
      popq rbx ++
      ret

let copy_struct = (*on copie la structure bit par bit*)
  let fin = new_label () in
    label "copie" ++
      testq (reg rdx) (reg rdx) ++ (*pour la boucle*)
      jz fin ++     (*on parcourt la structure grâce à une boucle et on sort grâce au label fin*)
      movq (ind rdi) (reg rcx) ++
      movq (reg rcx) (ind rsi) ++
      addq (imm 8) (reg rdi) ++
      addq (imm 8) (reg rsi) ++
      subq (imm 8) (reg rdx) ++
      jmp "copie" ++
    label fin ++
      ret

let declaration = function
  | TDfunction _ -> ()
  | TDstruct s ->
    let ofs = ref 0 in
    Hashtbl.iter (fun _ f -> f.f_ofs <- !ofs; ofs := !ofs + (sizeof f.f_typ)) s.s_fields


let file ?debug:(b=false) dl =
  debug := b;
  let funs = List.fold_left decl nop dl in
  { text =
      globl "main" ++ label "main" ++
      call "F_main" ++
      xorq (reg rax) (reg rax) ++
      ret ++
      funs ++
      inline
           "\n\
            print_int:\n\
           \      movq     %rdi, %rsi\n\
           \      leaq     S_int, %rdi\n\
           \      xorq     %rax, %rax\n\
           \      call     printf \n\
           \      ret\n\
            print_string:\n\
           \      test    %rdi, %rdi\n\
           \      jz      print_nil\n\
           \      mov     %rdi, %rsi\n\
           \      leaq    S_string, %rdi\n\
           \      xorq    %rax, %rax\n\
           \      call    printf\n\
           \      ret\n\
            print_nil:\n\
           \      leaq    S_nil, %rdi\n\
           \      xorq    %rax, %rax\n\
           \      call    printf\n\
           \      ret\n\
            print_space:\n\
           \      leaq    S_space, %rdi\n\
           \      xorq    %rax, %rax\n\
           \      call    printf\n\
           \      ret\n\n\
            print_newline:\n\
           \      leaq    S_newline, %rdi\n\
           \      xorq    %rax, %rax\n\
           \      call    printf\n\
           \      ret\n\
            print_bool:\n\
           \      xorq    %rax, %rax\n\
           \      test    %rdi, %rdi\n\
           \      jz      1f\n\
           \      leaq    S_true, %rdi\n\
           \      call    printf\n\
           \      ret\n\
            1:    leaq     S_false, %rdi\n\
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
           \      ret\n"

    ;
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
    ++ (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop);
  }
  
