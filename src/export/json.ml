(** Export to json files. *)

open Extras
module B = Basic
module D = Dep
module E = Entry
module F = Format
module S = Signature
module T = Term
module U = Uri
module Jt = Json_types
module Tx = Taxonomy
module Th = Theories

(** The theory (or logic) used. *)
let _th = (`Sttfa)

(** [ppt_of_dkterm md tx te] converts Dedukti term [te] from Dedukti
    module [md] into a JSON ppterm of taxonomy [tx]. *)
let rec ppt_of_dkterm : B.mident -> Tx.Sttfa.t -> T.term -> Jt.Ppterm.t =
  fun md tx t ->
  ppt_of_dkterm_args md tx t []

(** [ppt_of_dkterm_args md tx te stk] converts Dedukti term [te] from
    module [md] applied to stack of arguments [stk].  [tx] is the taxon of
    [te]. *)
and ppt_of_dkterm_args : B.mident -> Tx.Sttfa.t -> T.term -> T.term list ->
  Jt.Ppterm.t =
  fun md tx t stk ->
  let ppt_of_dkterm = ppt_of_dkterm md tx in
  let ppt_of_dkterm_args = ppt_of_dkterm_args md tx in
  match t with
  | T.Kind -> Jt.Ppterm.Const { c_symb = "Kind" ; c_args = [] }
  | T.Type(_) -> Jt.Ppterm.Const { c_symb = "Type" ; c_args = [] }
  | T.DB(_,id,_) ->
    let v_args = List.map ppt_of_dkterm stk in
    Jt.Ppterm.Var { v_symb = B.string_of_ident id ; v_args}
  | T.Const(_,name) ->
    let c_args = List.map ppt_of_dkterm stk in
    let c_symb =
      let mid = B.md name in
      let id = B.id name in
      U.uri_of_dkid mid id _th tx |> U.to_string
    in
    Jt.Ppterm.Const { c_symb ; c_args }
  | T.App(t,u,vs) -> ppt_of_dkterm_args t (u :: vs @ stk)
  | T.Lam(_,id,annot,t) ->
    let bound = B.string_of_ident id in
    let annotation = Option.map ppt_of_dkterm annot in
    let b_args = List.map ppt_of_dkterm stk in
    Jt.Ppterm.Binder { b_symb = "λ" ; bound ; annotation
                     ; body = ppt_of_dkterm t ; b_args }
  | T.Pi(_,id,t,u) ->
    let annotation = Some(ppt_of_dkterm t) in
    let body = ppt_of_dkterm u in
    let bound = B.string_of_ident id in
    let b_args = List.map ppt_of_dkterm stk in
    Jt.Ppterm.Binder { b_symb = "Π" ; bound ; annotation ; body ; b_args }

(** [find_deps m i e] computes the list of all direct down dependencies
    of a Dedukti entry [e] with name [m.i]. *)
let find_deps : B.mident -> B.ident -> E.entry -> Jt.dependency list =
  fun mid id e ->
  D.compute_ideps := true; (* Compute dependencies of items *)
  D.make mid [e];
  match D.get_data (B.mk_name mid id) with
  | exception D.Dep_error(D.NameNotFound(_)) -> []
  | d ->
    (* Remove some elements from dependencies and create a part of the uri. *)
    let f n =
      if B.string_of_mident (B.md n) = Th.string_of_theory _th then None else
      let locator = String.concat "."
            [ B.string_of_mident (B.md n) ; B.string_of_ident (B.id n) ]
      in
      Some(locator)
    in
    List.filter_map f (D.NameSet.elements D.(d.down))

let item_of_entry : B.mident -> E.entry -> Jt.item option = fun md en ->
  match en with
  | Entry.Decl(_,id,_,t) ->
    let tx = Tx.Sttfa.of_decl t in
    let uri = U.uri_of_dkid md id _th tx |> U.to_string in
    let ppt_body =  ppt_of_dkterm md tx t in
    Some { name = uri
         ; taxonomy = Tx.Sttfa.to_string tx
         ; term = None
         ; body = ppt_body
         ; deps = find_deps md id en
         ; theory = []
         ; exp = [] }
  | Entry.Def(_,id,_,teo,te)  ->
    let tx = Tx.Sttfa.of_def te in
    let uri = U.uri_of_dkid md id _th tx |> U.to_string in
    let ppt_body = ppt_of_dkterm md tx te in
    let ppt_term_opt = Option.map (ppt_of_dkterm md tx) teo in
    Some { name = uri
         ; taxonomy = Tx.Sttfa.to_string tx
         ; term = ppt_term_opt
         ; body = ppt_body
         ; deps = find_deps md id en
         ; theory = []
         ; exp = [] }
  | _                     -> None

let print_document : Format.formatter -> Jt.document -> unit = fun fmt doc ->
  Jt.document_to_yojson doc |> Yojson.Safe.pretty_print fmt
