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
  | ForallK (ty_var, ty) when ty_var = src ->
      ForallK (dst, rename_type src dst ty)
  | ForallK (ty_var,  _) when ty_var = dst ->
      raise VarNameAlreadyTaken
  | ForallK (ty_var, ty) ->
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
  | ForallP (ty_var, tm) when ty_var = src ->
      ForallP (dst, rename_term src dst tm)
  | ForallP (ty_var,  _) when ty_var = dst ->
      raise VarNameAlreadyTaken
  | ForallP (ty_var, tm) ->
      ForallP (ty_var, rename_term src dst tm)
  | Te _tm ->
      Te (rename__term src dst _tm)

let rename_judgment src dst { ty; te; hyp; thm } =
  {
    ty = List.map (fun ty_var -> if ty_var = src then dst else if ty_var = dst then raise VarNameAlreadyTaken else ty_var) ty;
    te = List.map (fun (tm_var, _ty) -> (tm_var, rename__type src dst _ty)) te;
    hyp = TeSet.map (fun (prf_var, _tm) -> (prf_var, rename__term src dst _tm)) hyp;
    thm = rename_term src dst thm
  }

let rename_proof src dst =
  let rename__type = rename__type src dst in
  let rename__term = rename__term src dst in
  let rename_judgment = rename_judgment src dst in
  let rec rename_proof = function
    | Assume (j, prf_var) ->
        Assume (rename_judgment j, prf_var)
    | Lemma (name, j) ->
        Lemma (name, rename_judgment j)
    | Conv (j, prf, trace) ->
        Conv (rename_judgment j, rename_proof prf, trace)
    | ImplE (j, prfpq, prfp) ->
        ImplE (rename_judgment j, rename_proof prfpq, rename_proof prfp)
    | ImplI (j, prf, prf_var) ->
        ImplI (rename_judgment j, rename_proof prf, prf_var)
    | ForallE (j, prf, _te) ->
        ForallE (rename_judgment j, rename_proof prf, rename__term _te)
    | ForallI (j, prf, te_var) ->
        ForallI (rename_judgment j, rename_proof prf, te_var)
    | ForallPE (j, prf, _ty) ->
        ForallPE (rename_judgment j, rename_proof prf, rename__type _ty)
    | ForallPI (j, prf, ty_var) when ty_var = src ->
        ForallPI (rename_judgment j, rename_proof prf, dst)
    | ForallPI (_,   _, ty_var) when ty_var = dst ->
        raise VarNameAlreadyTaken
    | ForallPI (j, prf, ty_var) ->
        ForallPI (rename_judgment j, rename_proof prf, ty_var)
    in rename_proof

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
  (* let rec rename_type_variables_judgment ({ ty; _ } as j) =
    match ty with
    | [] -> j, []
    | ty_var :: ty_tl -> begin
      let dst = type_var_generator () in
      let new_j = rename_judgment ty_var dst { j with ty = ty_tl } in
      let renamed_j, renamings = rename_type_variables_judgment new_j in
      { renamed_j with ty = dst :: renamed_j.ty }, (ty_var, dst) :: renamings
    end
  in *)
  let rec rename_type_variables_proof = function
    | Assume (j, prf_var) -> Assume (j, prf_var), []
    | Lemma (name, j) -> Lemma (name, j), []
    | Conv (j, prf, trace) ->
        let renamed_prf, renamings = rename_type_variables_proof prf in
        Conv (j, renamed_prf, trace), renamings
    | ImplE (j, prfpq, prfp) ->
        let renamed_prfpq, renamings1 = rename_type_variables_proof prfpq in
        let renamed_prfp, renamings2 = rename_type_variables_proof prfp in
        ImplE (j, renamed_prfpq, renamed_prfp), renamings1 @ renamings2
    | ImplI (j, prf, prf_var) ->
        let renamed_prf, renamings = rename_type_variables_proof prf in
        ImplI (j, renamed_prf, prf_var), renamings
    | ForallE (j, prf, _te) ->
        let renamed_prf, renamings = rename_type_variables_proof prf in
        ForallE (j, renamed_prf, _te), renamings
    | ForallI (j, prf, te_var) ->
        let renamed_prf, renamings = rename_type_variables_proof prf in
        ForallI (j, renamed_prf, te_var), renamings
    | ForallPE (j, prf, _ty) ->
        let renamed_prf, renamings = rename_type_variables_proof prf in
        ForallPE (j, renamed_prf, _ty), renamings
    | ForallPI (j, prf, ty_var) -> begin try
          let dst = type_var_generator () in
          let new_prf = rename_proof ty_var dst prf in
          let renamed_prf, renamings = rename_type_variables_proof new_prf in
          ForallPI (j, renamed_prf, dst), (ty_var, dst) :: renamings
        with VarNameAlreadyTaken -> rename_type_variables_proof (ForallPI (j, prf, ty_var))
      end
  in
  let rec rename_type_variables_both ty tm =
    try
      let renamed_ty, renamings = rename_type_variables_type ty in
      let renamed_tm_once = List.fold_left (fun tm (src, dst) -> rename_term src dst tm) tm renamings in
      renamed_ty, fst @@ rename_type_variables_term renamed_tm_once
    with
      VarNameAlreadyTaken -> rename_type_variables_both ty tm
  in
  let rec rename_type_variables_three ty tm prf =
    try
      let renamed_ty, renamings = rename_type_variables_type ty in
      let renamed_tm_once = List.fold_left (fun tm (src, dst) -> rename_term src dst tm) tm renamings in
      let renamed_prf_once = List.fold_left (fun tm (src, dst) -> rename_proof src dst tm) prf renamings in
      let renamed_tm, renamings = rename_type_variables_term renamed_tm_once in
      let renamed_prf_twice = List.fold_left (fun tm (src, dst) -> rename_proof src dst tm) renamed_prf_once renamings in
      let renamed_prf, _ = rename_type_variables_proof renamed_prf_twice in
      renamed_ty, renamed_tm, renamed_prf
    with
      VarNameAlreadyTaken -> rename_type_variables_three ty tm prf
  in
  match item with
  | Definition (name, ty, tm) ->
      let ty, tm = rename_type_variables_both ty tm in
      Definition (name, ty, tm)
  | Axiom (name, tm) ->
      let tm, _ = rename_type_variables_term tm in
      Axiom (name, tm)
  | Theorem (name, tm, proof) ->
      let _, tm, proof = rename_type_variables_three (Ty Prop) tm proof in
      Theorem (name, tm, proof)
  | Parameter (name, ty) ->
      let ty, _ = rename_type_variables_type ty in
      Parameter (name, ty)
  | TypeDecl (name, arity) -> TypeDecl (name, arity)
  | TypeDef (name, args, _ty) ->
      TypeDef (name, args, _ty)


let type_of__term tm_ctxt =
  let rec type_of__term = function
  | TeVar var -> List.assoc var tm_ctxt
  | Abs (_, _ty, _tm) | Forall (_, _ty, _tm) ->
      Arrow (_ty, type_of__term _tm)
  | App (_tm_left, _tm_right) | Impl (_tm_left, _tm_right) -> begin match type_of__term _tm_left with
      | Arrow (_ty_left, _ty_right) when _ty_left = type_of__term _tm_right -> _ty_right
      | _ -> assert false
  end
  | AbsTy (_, _tm) ->
      type_of__term _tm
  | Cst (_name, _tys) ->
      assert false
  in type_of__term

let type_of_term tm_ctxt =
  let rec type_of_term = function
  | Te _te -> type_of__term tm_ctxt _te
  | ForallP (_, te) -> type_of_term te
  in type_of_term

let cur_md = ref ""

let forbidden_id = ["bool"]
let valid_char c =
  let i = Char.code c in
  32 < i && i < 127 && not @@ List.mem c ['_']

let sanitize id =
  let id =
    if List.mem id forbidden_id || not @@ valid_char id.[0] then
      "logi_" ^ id
    else id
  in
  if not @@ valid_char id.[String.length id - 1] then
    id ^ "_logi"
  else id

let print_name fmt (md, id) =
  let id = sanitize id in
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
    (* print__type _ty *) Format.pp_print_string "_"

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

let rec print_proof fmt = function
  | Assume (_, prf_var) ->
      Format.fprintf fmt "%a"
        print_prf_var prf_var
  | Lemma (name, _) ->
      Format.fprintf fmt "%a"
        print_name name
  | ForallE (_, proof, u) ->
      let j = judgment_of proof in
      let (tm_var, _ty, _tm_right) = j.thm |> function Te Forall (tm_var, _ty, _tm_right) -> (tm_var, _ty, _tm_right) | _ -> assert false in
      Format.fprintf fmt "spec@ %a TYPE(%a)@ %a (%a)@ %a (%a)@ %a (Pure.PClass type_class %a TYPE(%a))@ %a (%a)"
        print_as_1 "\\<cdot>"
        print__type _ty
        print_as_1 "\\<cdot>"
        print__term (Abs (tm_var, _ty, _tm_right))
        print_as_1 "\\<cdot>"
        print__term u
        print_as_1 "\\<bullet>"
        print_as_1 "\\<cdot>"
        print__type _ty
        print_as_1 "\\<bullet>"
        print_proof proof
  | ForallI (_, proof, tm_var) ->
      let j = judgment_of proof in
      let tm__type = List.assoc tm_var j.te in
      Format.fprintf fmt "allI@ %a TYPE(%a)@ %a (%a)@ %a (Pure.PClass type_class %a TYPE(%a))@ %a (%a%a.@ %a)"
        print_as_1 "\\<cdot>"
        print__type tm__type
        print_as_1 "\\<cdot>"
        print_term j.thm
        print_as_1 "\\<bullet>"
        print_as_1 "\\<cdot>"
        print__type tm__type
        print_as_1 "\\<bullet>"
        print_as_1 "\\<^bold>\\<lambda>"
        print_tm_var tm_var
        print_proof proof
  | ImplE (_, prfpq, prfp) ->
      let j = judgment_of prfpq in
      let (_tm_left, _tm_right) = j.thm |> function Te Impl (_tm_left, _tm_right) -> (_tm_left, _tm_right) | _ -> assert false in
      Format.fprintf fmt "mp@ %a (%a)@ %a (%a)@ %a (%a)@ %a (%a)"
        print_as_1 "\\<cdot>"
        print__term _tm_left
        print_as_1 "\\<cdot>"
        print__term _tm_right
        print_as_1 "\\<bullet>"
        print_proof prfpq
        print_as_1 "\\<bullet>"
        print_proof prfp
  | ImplI (_, proof, prf_var) ->
      let j = judgment_of proof in
      let prf_prop = j.hyp |> TeSet.to_seq |> List.of_seq |> List.assoc prf_var in
      Format.fprintf fmt "impI@ %a (%a)@ %a (%a)@ %a (Pure.AbsP@ (%a)@ (%a%a.@ %a))"
        print_as_1 "\\<cdot>"
        print__term prf_prop
        print_as_1 "\\<cdot>"
        print_term j.thm
        print_as_1 "\\<bullet>"
        print__term prf_prop
        print_as_1 "\\<lambda>"
        print_prf_var prf_var
        print_proof proof
  | ForallPE (_, proof, _ty) ->
      Format.fprintf fmt "%a"
        print_proof proof
        (* print__type _ty *)
  | ForallPI (_, proof, _ty_var) ->
      Format.fprintf fmt "%a"
        (* print_ty_var ty_var *)
        print_proof proof
  | Conv (_, proof, _trace) ->
      Format.fprintf fmt "%a"
        print_proof proof
        (* print_trace trace *)

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
      Format.fprintf fmt "@[theorem_from_proof %s:@ %a@]@ @[<v2>: %a@]"
        (sanitize id)
        (print_cartouched print_term) tm
        (print_cartouched print_proof) proof
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
    Format.fprintf fmt "@[<v2>theory %s@,@[<2>imports Main Theorem_from_proof%a@]@,keywords \"theorem_from_proof\" :: thy_decl@]@,@[<v2>begin@,%a@]@,end@."
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

fun mk_thm ((name, prop), proof) (thy: theory) =
  let
    val ctxt = Proof_Context.init_global thy;
    val prop = Syntax.parse_prop ctxt prop;
    val prop = singleton (Syntax.check_props ctxt) prop;
    val proof = Proof_Syntax.read_proof thy false false proof;
    val proof = Proofterm.reconstruct_proof thy prop proof;
    val thm = Proof_Checker.thm_of_proof thy proof
  in
  Global_Theory.store_thm (name, thm) thy |> snd
end
val () =
  Outer_Syntax.command \<^command_keyword>\<open>theorem_from_proof\<close>
    "declare a prop and prove it using exact proof"
    (Parse.binding --| Parse.$$$ ":" -- Parse.prop --| Parse.$$$ ":" -- Parse.text
      >> (Toplevel.theory o mk_thm));
›
*)
