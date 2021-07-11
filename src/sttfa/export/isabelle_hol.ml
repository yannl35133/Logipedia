open Ast

let to_printer s fmt () = Format.fprintf fmt s
let print_as_1 fmt = Format.pp_print_as fmt 1

let print_list_if_non_empty ?(pp_beg=fun _ () -> ()) ?(pp_end=fun _ () -> ()) ?(pp_sep=Format.pp_print_cut) pp_element fmt l =
  if l = [] then
    ()
  else
    Format.fprintf fmt "%a%a%a"
      pp_beg ()
      (Format.pp_print_list ~pp_sep pp_element) l
      pp_end ()

let generate_type_variables =
  let alphabet = String.init 26 (fun i -> Char.(chr (i + code 'a'))) in
  let nth n =
    "'" ^ String.make 1 alphabet.[n mod 26] ^ (if n < 26 then "" else string_of_int (n / 26))
  in
  fun () ->
    let c = ref (-1) in
    fun () ->
    incr c; nth !c


exception VarNameAlreadyTaken

let rename__type src dst =
  let rec rename__type = function
  | TyVar var -> if var = src then TyVar dst else TyVar var
  | Arrow (_ty_left, _ty_right) ->
    Arrow (rename__type _ty_left, rename__type _ty_right)
  | TyOp (tyop, _tys) ->
    TyOp (tyop, List.map rename__type _tys)
  | Prop -> Prop
  in rename__type

let rec rename_type src dst = function
  | ForallK (ty_var, ty) ->
      if ty_var = src then
        raise VarNameAlreadyTaken
      else
        ForallK (ty_var, rename_type src dst ty)
  | Ty _ty ->
      Ty (rename__type src dst _ty)


let rename__term src dst =
  let rename__type = rename__type src dst in
  let rec rename__term = function
  | TeVar var -> TeVar var
  | Abs (var, _ty, _tm) ->
      Abs (var, rename__type _ty, rename__term _tm)
  | App (_tm_left, _tm_right) ->
      App (rename__term _tm_left, rename__term _tm_right)
  | Forall (var, _ty, _tm) ->
      Forall (var, rename__type _ty, rename__term _tm)
  | Impl (_tm_left, _tm_right) ->
      Impl (rename__term _tm_left, rename__term _tm_right)
  | AbsTy (ty_var, _tm) ->
      AbsTy (ty_var, rename__term _tm)
  | Cst (name, _tys) ->
      Cst (name, List.map rename__type _tys)
  in rename__term


let rec rename_term src dst = function
  | ForallP (ty_var, tm) ->
      if ty_var = src then
        raise VarNameAlreadyTaken
      else
        ForallP (ty_var, rename_term src dst tm)
  | Te _tm ->
      Te (rename__term src dst _tm)



let rename_type_variables item =
  let type_var_generator = generate_type_variables () in
  let rec rename_type_variables_type = function
    | ForallK (ty_var, ty) -> begin try
          let dst = type_var_generator () in
          let new_ty = rename_type ty_var dst ty in
          let renamed_ty, renamings = rename_type_variables_type new_ty in
          ForallK (dst, renamed_ty), (ty_var, dst) :: renamings
        with VarNameAlreadyTaken -> rename_type_variables_type (ForallK (ty_var, ty))
      end
    | Ty _ty -> Ty _ty, []
  in
  let rec rename_type_variables_term = function
  | ForallP (ty_var, tm) -> begin try
        let dst = type_var_generator () in
        let new_tm = rename_term ty_var dst tm in
        let renamed_tm, renamings = rename_type_variables_term new_tm in
        ForallP (dst, renamed_tm), (ty_var, dst) :: renamings
      with VarNameAlreadyTaken -> rename_type_variables_term (ForallP (ty_var, tm))
    end
  | Te _tm -> Te _tm, []
  in
  let rec rename_type_variables_both ty tm =
    try
      let renamed_ty, renamings = rename_type_variables_type ty in
      let renamed_tm_once = List.fold_left (fun tm (src, dst) -> rename_term src dst tm) tm renamings in
      renamed_ty, fst @@ rename_type_variables_term renamed_tm_once
    with
      VarNameAlreadyTaken -> rename_type_variables_both ty tm
  in
  match item with
  | Definition (name, ty, tm) ->
      let ty, tm = rename_type_variables_both ty tm in
      Definition (name, ty, tm)
  | Axiom (name, tm) ->
      let tm, _ = rename_type_variables_term tm in
      Axiom (name, tm)
  | Theorem (name, tm, proof) ->
      let tm, _ = rename_type_variables_term tm in
      Theorem (name, tm, proof)
  | Parameter (name, ty) ->
      let ty, _ = rename_type_variables_type ty in
      Parameter (name, ty)
  | TypeDecl (name, arity) -> TypeDecl (name, arity)
  | TypeDef (name, args, _ty) ->
      TypeDef (name, args, _ty)


let cur_md = ref ""

let sanitize id =
  (* let u_id = String.uncapitalize_ascii id in
  if List.mem id !forbidden_id || List.mem u_id !forbidden_id then
    (*let () = Printf.printf "OOPS, issue with %s or %s, replacing by %s.\n" id u_id ("mat_"^id) in*)
    "mat_"^id
  else if b then u_id
  else id *)
  (* Format.eprintf "[WARNING] Id sanitization is not implemented@."; *)
  id

let print_name fmt (md, id) =
  let id = sanitize id in
  let md = sanitize md in
  if !cur_md = md then
    Format.fprintf fmt "%s" id
  else
    Format.fprintf fmt "%s.%s" md id

let print_ty_var = Format.pp_print_string

let rec print__type fmt = function
  | TyVar var ->
      Format.fprintf fmt "%a" print_ty_var var
  | Arrow (_ty_left, _ty_right) ->
      Format.fprintf fmt "%a@ %a %a"
        print__type_at _ty_left
        print_as_1 "\\<Rightarrow>"
        print__type _ty_right
  | TyOp (tyop, _tys) ->
      Format.fprintf fmt "%a%a"
        (print_list_if_non_empty ~pp_beg:(to_printer "(") ~pp_sep:(to_printer ",@ ") ~pp_end:(to_printer ")@ ") print__type) _tys
        print_name tyop
  | Prop ->
      Format.fprintf fmt "%s" "bool"
and print__type_at fmt = function
  | Arrow _ | TyOp (_, _ :: _) as _ty -> Format.fprintf fmt "(%a)" print__type _ty
  | _ty -> print__type fmt _ty


let rec print_type fmt = function
  | ForallK (ty_var, ty) ->
      Format.fprintf fmt "@[<2>%a %a%a%a.%a@ %a@]"
        print_as_1 "\\<comment>"
        print_as_1 "\\<open>"
        print_as_1 "\\<forall>"
        print_ty_var ty_var
        print_as_1 "\\<close>"
        print_type ty
  | Ty _ty ->
      print__type fmt _ty


let print_tm_var = Format.pp_print_string

let print_typed_tm_var fmt (var, _ty) =
  Format.fprintf fmt "@[%a@ :: %a@]"
    print_tm_var var
    print__type _ty

let rec print__term fmt = function
  | TeVar var ->
      Format.fprintf fmt "%a" print_tm_var var
  | Abs (var, _ty, _tm) ->
      Format.fprintf fmt "@[<2>%a%a.@ %a@]"
        print_as_1 "\\<lambda>"
        print_typed_tm_var (var, _ty)
        print__term _tm
  | App (App _ as _tm_left, _tm_right) ->
      Format.fprintf fmt "%a@ %a"
        print__term     _tm_left
        print__term_app _tm_right
  | App (_tm_left, _tm_right) ->
      Format.fprintf fmt "%a@ %a"
        print__term_app _tm_left
        print__term_app _tm_right
  | Forall (var, _ty, _tm) ->
      Format.fprintf fmt "@[<2>%a%a.@ %a@]"
        print_as_1 "\\<forall>"
        print_typed_tm_var (var, _ty)
        print__term _tm
  | Impl (_tm_left, (Impl _ as _tm_right)) ->
      Format.fprintf fmt "%a@ %a %a"
        print__term_impl _tm_left
        print_as_1 "\\<longrightarrow>"
        print__term      _tm_right
  | Impl (_tm_left, _tm_right) ->
      Format.fprintf fmt "%a@ %a %a"
        print__term_impl _tm_left
        print_as_1 "\\<longrightarrow>"
        print__term_impl _tm_right
  | AbsTy (ty_var, _tm) ->
      Format.fprintf fmt "@[<2>%a %a%a%a.%a@ %a@]"
        print_as_1 "\\<comment>"
        print_as_1 "\\<open>"
        print_as_1 "\\<lambda>"
        print_ty_var ty_var
        print_as_1 "\\<close>"
        print__term _tm
  | Cst (name, _tys) ->
      let pp_beg fmt () =
        Format.fprintf fmt "@ %a %a"
          print_as_1 "\\<comment>"
          print_as_1 "\\<open>"
      in
      let pp_end fmt () = print_as_1 fmt "\\<close>" in
      Format.fprintf fmt "%a%a"
        print_name name
        (print_list_if_non_empty ~pp_beg ~pp_end ~pp_sep:Format.pp_print_space print__type_at) _tys
and print__term_impl fmt = function
  | Abs _ | Forall _ | Impl _ | AbsTy _ | Cst (_, _ :: _) as _tm -> Format.fprintf fmt "(%a)" print__term _tm
  | _tm -> print__term fmt _tm
and print__term_app fmt = function
  | Abs _ | App _ | Forall _ | Impl _ | AbsTy _ | Cst (_, _ :: _) as _tm -> Format.fprintf fmt "(%a)" print__term _tm
  | _tm -> print__term fmt _tm

let rec print_term fmt = function
  | ForallP (ty_var, tm) ->
    Format.fprintf fmt "@[<2>%a %a%a%a.%a@ %a@]"
      print_as_1 "\\<comment>"
      print_as_1 "\\<open>"
      print_as_1 "\\<forall>"
      print_ty_var ty_var
      print_as_1 "\\<close>"
      print_term tm
  | Te _tm ->
      print__term fmt _tm

let print_prf_var = Format.pp_print_string

let print_judgment fmt { ty; te = tm; hyp; thm } =
  let comma_sep = to_printer ",@ " in
  Format.fprintf fmt "@[[To reach judgement %a%a%a@ |- %a]@]"
    (print_list_if_non_empty ~pp_sep:comma_sep ~pp_end:comma_sep
      (fun fmt ty_var ->
        Format.fprintf fmt "%a :: Type"
          print_ty_var ty_var)) ty
    (print_list_if_non_empty ~pp_sep:comma_sep ~pp_end:comma_sep
      (fun fmt (tm_var, _ty) ->
        Format.fprintf fmt "%a :: %a"
          print_tm_var tm_var
          print__type _ty)) tm
    (print_list_if_non_empty ~pp_sep:comma_sep ~pp_end:comma_sep
      (fun fmt (prf_var, _tm) ->
        Format.fprintf fmt "%a :: %a"
          print_prf_var prf_var
          print__term _tm)) (List.of_seq @@ TeSet.to_seq @@ hyp)
    print_term thm

let rec print_proof fmt = function
  | Assume (j, prf_var) ->
      Format.fprintf fmt "@[%a@ Assume %a@]@,"
        print_judgment j
        print_prf_var prf_var
  | Lemma (name, j) ->
      Format.fprintf fmt "@[%a@ Apply lemma %a@]@,"
        print_judgment j
        print_name name
  | ForallE (j, proof, u) ->
      Format.fprintf fmt "%a@[%a@ From above, apply forallE with term %a@]@,"
        print_proof proof
        print_judgment j
        print__term u
  | ForallI (j, proof, tm_var) ->
      Format.fprintf fmt "%a@[%a@ From above, apply forallI with term_var %a@]@,"
        print_proof proof
        print_judgment j
        print_tm_var tm_var
  | ImplE (j, prfpq, prfp) ->
      Format.fprintf fmt "%a@,@[<v2>Apply implE on implication proof@ %a@]@ @[<v2>with hypothesis proof@ %a@]@,"
        print_judgment j
        print_proof prfpq
        print_proof prfp
  | ImplI (j, proof, prf_var) ->
      Format.fprintf fmt "%a@[%a@ From above, apply implI with hypothesis name %a@]@,"
        print_proof proof
        print_judgment j
        print_prf_var prf_var
  | ForallPE (j, proof, _ty) ->
      Format.fprintf fmt "%a@[%a@ From above, apply forallPE with type %a@]@,"
        print_proof proof
        print_judgment j
        print__type _ty
  | ForallPI (j, proof, ty_var) ->
      Format.fprintf fmt "%a@[%a@ From above, apply forallPI with type_var %a@]@,"
        print_proof proof
        print_judgment j
        print_ty_var ty_var
  | Conv (j, proof, trace) ->
      Format.fprintf fmt "%a@[%a@ From above, apply conversion with trace %a@]@,"
        print_proof proof
        print_judgment j
        print_trace trace

let print_cartouched printer fmt el =
  Format.fprintf fmt "%a%a%a"
    print_as_1 "\\<open>"
    printer el
    print_as_1 "\\<close>"

let print_arity fmt n =
  if n = 0 then () else
  let type_var_generator = generate_type_variables () in
  let type_vars = List.init n (fun _ -> type_var_generator ()) in
  Format.(
    fprintf fmt "@[<2>(%a@])@ "
      (pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt ",@ ") pp_print_string) type_vars
  )


let print_item fmt =
  function
  | Definition ((_, id), ty, tm) ->
      Format.fprintf fmt "@[definition %s@ :: %a@]@ where %a%s \\<equiv> %a%a"
        (sanitize id)
        (print_cartouched print_type) ty
        print_as_1 "\\<open>"
        id
        print_term tm
        print_as_1 "\\<close>"
  | Axiom ((_, id), tm) ->
      Format.fprintf fmt "@[<2>axiomatization where %s:@ %a@]"
        (sanitize id)
        (print_cartouched print_term) tm
  | Theorem ((_, id), tm, proof) ->
      Format.fprintf fmt "@[theorem %s:@ %a@]@ @[<v2>proof@,%a@]@,qed"
        (sanitize id)
        (print_cartouched print_term) tm
        print_proof proof
  | Parameter ((_, id), ty) ->
      Format.fprintf fmt "@[<2>consts %s@ :: %a@]"
        (sanitize id)
        (print_cartouched print_type) ty
  | TypeDecl ((_, id), arity) ->
      Format.fprintf fmt "@[<2>typedecl %a%s@]"
        print_arity arity
        (sanitize id)
  | TypeDef _ -> failwith "[Isabelle/HOL] Type definitions not handled right now"

let print_ast : Format.formatter -> Ast.ast -> unit =
  fun fmt ast ->
    cur_md := ast.md;
    Format.set_margin 120;
    Format.fprintf fmt "@[<v>theory %s@,@[<2>imports Main%a@]@,@[<v2>begin@,%a@]@,end@]@."
      ast.md
      (fun fmt -> D.QSet.iter (Format.fprintf fmt " %s")) ast.dep
      Format.(pp_print_list print_item) (List.map rename_type_variables ast.items)

(* Compatibility with Logipedia's API ([mdeps] is discarded) *)
let print_ast : Format.formatter -> ?mdeps:Ast.mdeps -> Ast.ast -> unit =
  fun fmt ?mdeps:_ ast ->
    print_ast fmt ast

(*
theory Scratch
  imports Main
  keywords "theorem_from_proof" :: thy_decl
begin

ML ‹

fun mk_thm ((name, prop), proof) (lthy: local_theory) =
  let
    val ctxt = lthy;
    val thy = Proof_Context.theory_of lthy;
    val prop = Syntax.parse_prop ctxt prop;
    val prop = singleton (Syntax.check_props ctxt) prop;
    val proof = Proof_Syntax.read_proof thy false true proof;
    val proof = Proofterm.reconstruct_proof thy prop proof;
    val thm = Proof_Checker.thm_of_proof thy proof
  in
  Local_Theory.note ((name, []), [thm]) lthy |> snd
end;

val () =
  Outer_Syntax.local_theory \<^command_keyword>‹theorem_from_proof›
    "declare a prop and prove it using exact proof"
    (Parse.binding --| Parse.$$$ ":" -- Parse.prop --| Parse.$$$ ":" -- Parse.text
      >> mk_thm);
›
*)
