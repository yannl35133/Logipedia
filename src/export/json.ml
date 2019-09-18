(** Export to json files. *)

open Extras
module F = Format
module Jt = Json_types
module B = Basic
module T = Term
module S = Signature
module D = Dep

(* Translate Dedukti term into Json ppt*)
let rec ppt_of_dkterm : T.term -> Jt.Ppterm.t = fun t ->
  ppt_of_dkterm_args t []

and ppt_of_dkterm_args : T.term -> T.term list -> Jt.Ppterm.t =
  fun t stk ->
  match t with
  | T.Kind -> Jt.Ppterm.Const { c_symb = ["Kind"] ; c_args = [] }
  | T.Type(_) -> Jt.Ppterm.Const { c_symb = ["Type"] ; c_args = [] }
  | T.DB(_,id,_) ->
    let v_args = List.map ppt_of_dkterm stk in
    Jt.Ppterm.Var { v_symb = Basic.string_of_ident id ; v_args}
  | T.Const(_,name) ->
    let c_args = List.map ppt_of_dkterm stk in
    let c_symb = [B.id name |> B.string_of_ident] in
    Jt.Ppterm.Const { c_symb ; c_args }
  | T.App(t,u,vs) -> ppt_of_dkterm_args t (u :: vs @ stk)
  | T.Lam(_,id,annot,t) ->
    let bound = B.string_of_ident id in
    let annotation = Option.bind ppt_of_dkterm annot in
    let b_args = List.map ppt_of_dkterm stk in
    Jt.Ppterm.Binder { b_symb = "λ" ; bound ; annotation
                     ; body = ppt_of_dkterm t ; b_args }
  | T.Pi(_,id,t,u) ->
    let annotation = Some(ppt_of_dkterm t) in
    let body = ppt_of_dkterm u in
    let bound = B.string_of_ident id in
    let b_args = List.map ppt_of_dkterm stk in
    Jt.Ppterm.Binder { b_symb = "Π" ; bound ; annotation ; body ; b_args }

(* Find direct dependencies of a Dedukti entry *)

let empty_mident = B.mk_mident ""

let find_deps : B.name -> Entry.entry -> D.data = fun name e ->
  D.make (B.md name) [e];
  D.get_data name

let item_of_entry : Entry.entry -> Jt.item option = function
  | Entry.Decl(_,id,static,t)  ->
    let ax_or_cst static = if static = S.Static then Uri.TxCst else Uri.TxAxm in
    let ppt = ppt_of_dkterm t in
    Some { name = B.string_of_ident id
         ; taxonomy = ax_or_cst static
         ; term = None
         ; body = ppt
         ; deps = []
         ; theory = []
         ; exp = [] }
  | Entry.Def(_,id,opacity,teo,te)  ->
    let  thm_or_def opacity = if opacity then Uri.TxDef else Uri.TxThm in
    Some { name = B.string_of_ident id
         ; taxonomy = thm_or_def opacity
         ; term = Option.bind ppt_of_dkterm teo
         ; body = ppt_of_dkterm te
         ; deps = []
         ; theory = []
         ; exp = [] }
  | _                     -> None

let print_document : Format.formatter -> Jt.document -> unit = fun fmt doc ->
  Jt.document_to_yojson doc |> Yojson.Safe.pretty_print fmt
