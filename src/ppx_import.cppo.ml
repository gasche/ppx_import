#if OCAML_VERSION < (4, 03, 0)
#define Cstr_tuple(x) x
#define Pcstr_tuple(x) x
#endif

open Longident
open Asttypes
open Parsetree
open Ast_mapper
open Ast_helper
open Types
open Ident

let raise_errorf ?sub ?if_highlight ?loc message =
  message |> Printf.kprintf (fun str ->
    let err = Location.error ?sub ?if_highlight ?loc str in
    raise (Location.Error err))

let replace_loc loc =
  { default_mapper with location = fun _ _ -> loc }

let lazy_env = lazy (
  (* It is important that the typing environment is not evaluated
     right away, but only once the ppx-context has been loaded from
     the AST, so that Config.load_path and the rest of the environment
     context are correctly set.

     The environment setting should happen when reading the
     ppx-context attribute which is the very first structure/signature
     item sent to ppx rewriters. In particular, this happens before
     the [%import ] extensions are traversed, which are the places in
     this code where 'env' is forced.

     We would also have the option to not have a global environment, but
     recompute the typing environment on each [%import ] extension. We don't
     see any advantage in doing this, given that we compute the global/initial
     environment that is the same at all program points.
  *)
  Compmisc.init_path false;
  Compmisc.initial_env ()
)

let string_of_lid lid =
  let rec print lid acc = match lid with
    | Longident.Lident s -> s::acc
    | Longident.Ldot (lid, id) -> print lid ("." :: id :: acc)
    | Longident.Lapply (la, lb) -> print la ("(" :: print lb (")" :: acc))
  in String.concat "" (print lid [])

(* Note on a subtle implementation.

   The strategy to resolve the import of a path `M.N.t` is made
   complex by the fact that ppx_import does not require `M.N` to be
   a valid module path in the current typing environment.

   Indeed, it supports the following

   file M.ml:

       module type S = struct
         type t = int
       end

   file foo.ml:

       [%%import M.S.t]

   where `M.S` is not the path to a sub-module, but to a submodule-type:
   `M.S.t` is not a valid OCaml path, but it is understood by [%%import]
   as an access to the field `t` of the module type `S`.

   In the general case, a path is of the form `V.P.f`, where:

   - `V` is a valid module path, possibly empty
   - `P` is an invalid module path, either empty or
     starting with a module type name `T`
   - `f` is the last field name, either a type name `t`
     or a module type name `T`

   If `V` and `P` are empty, our path is just a single name `t` or `T`.
   It is resolved by calling the type-checker in the ambient (global)
   type environment. This is done within the main functions
   `type_declaration` and `module_type`.

   Otherwise, the split between `V` and `P` is computed in the
   `find_prefix` subroutine of `find_sig`, and the signature
   of `V` asked to the type-checker. The signature of `V.P` is
   then computed by iterating the `get_subsig` function over `P`.
   Finally, the lookup of `f` in the signature of `V.P` is done
   by the auxiliary functions `get_type_decl` and `get_modtype_decl`,
   called from the main functions `type_declaration` and `module_type`.
*)

let open_module_type env loc lid module_type =
  (* TODO: check if scrape_alias is the right thing,
     it seems to strengthen the signature, maybe we should
     expand the aliases manually *)
  match Env.scrape_alias env module_type with
  | ( Mty_ident _
    | Mty_alias _
    | Mty_functor _
    ) ->
    raise_errorf ~loc "[%%import]: cannot access the components of %s"
      (string_of_lid lid)
  | Mty_signature sig_items -> sig_items

let open_module_decl env loc lid module_decl =
  open_module_type env loc lid module_decl.md_type

let open_modtype_decl env loc lid modtype_decl =
  match modtype_decl.mtd_type with
  | None ->
    raise_errorf ~loc
      "[%%import]: cannot access the components of abstract module type %s"
      (string_of_lid lid)
  | Some module_type ->
    open_module_type env loc lid module_type

let get_subsig loc (lid, sig_items) field =
  let rec loop sig_items =
    match sig_items with
    | Sig_module (id, { md_type = Mty_signature sig_items }, _) :: _
      when Ident.name id = field ->
      (Ldot (lid, field), sig_items)
    | Sig_modtype (id, { mtd_type = Some (Mty_signature sig_items) }) :: _
      when Ident.name id = field ->
      (Ldot (lid, field), sig_items)
    | _ :: sig_items ->
      loop sig_items
    | [] ->
      raise_errorf ~loc "[%%import]: cannot locate component %s.%s"
        (string_of_lid lid) field
  in
  loop sig_items

type find_prefix_result =
  | Empty_prefix of head * suffix
  | Module_prefix of Longident.t * module_declaration * suffix
and head = string
and suffix = string list

(* [%%import V.P.f] results in a call to `find_sig ~loc V.P`:
   the `lid` argument is the parent of the full imported path,
   and `find_sig` returns its interface as a list of signature
   items (or fails with an error). *)
let find_sig ~loc lid =
  let env = Lazy.force lazy_env in
  let rec find_prefix lid suffix =
    (* Note: we are careful to call `Env.lookup_module` and not
       `Typetexp.lookup_module`, because we want to reason precisely
       about the possible failures: we want to handle the case where
       the module path does not exist, but let all the other errors
       (invalid .cmi format, etc.) bubble up to the error handler.

       `Env.lookup_module` allows to do this easily as it raises
       a well-identified `Not_found` exception, while
       `Typetexp.lookup_module` wraps the Not_found failure in
       user-oriented data and is not meant for catching.

       `Env.find_module` can raise `Not_found` again; we suspect that
       it will not in the cases where `lookup_module` returned correctly,
       but better be safe and bundle them in the same try..with.
    *)
    match
      (try
         Some (Env.find_module (Env.lookup_module ~load:true lid env) env)
       with Not_found -> None)
    with
    | Some module_decl ->
      Module_prefix (lid, module_decl, suffix)
    | None ->
      begin match lid with
        | Longident.Ldot (lid, field) -> find_prefix lid (field :: suffix)
        | Longident.Lident head -> Empty_prefix (head, suffix)
        | Longident.Lapply _ ->
          raise_errorf ~loc "[%%import]: invalid applied path %s"
            (string_of_lid lid)
      end
  in
  let sig_items, suffix =
    match find_prefix lid [] with
    | Module_prefix (lid, module_decl, suffix) ->
      open_module_decl env loc lid module_decl, suffix
    | Empty_prefix (head, suffix) ->
      (* if the head is not a valid module, it must be a module type *)
      let head_id = Longident.Lident head in
      match
        (* Here again we prefer to handle the `Not_found` case, so we
           use `Env.lookup_module` rather than `Typetexp.lookup_module`.

           Because we just fail in the `Not_found` case we could call
           `Env.lookup_modtype` and not handle the failure (the user
           would get a nice error message), but are not sure whether
           the user intends to have written a module name or module
           type name, so an error in terms of module-type only could
           be confusing.
        *)
        (try Some (Env.lookup_modtype ~loc head_id env) with Not_found -> None)
      with
      | None ->
        raise_errorf ~loc "[%%import] invalid import path %s" (string_of_lid lid)
      | Some (_path, modtype_decl) ->
        open_modtype_decl env loc head_id modtype_decl, suffix
  in
  let (_lid, sig_items) =
    List.fold_left (get_subsig loc) (lid, sig_items) suffix in
  sig_items

let get_sig_item f ~loc sig_items parent_id field =
  let rec loop sig_items =
    match sig_items with
    | item :: sig_items ->
      (match f field item with Some x -> x | None -> loop sig_items)
    | [] -> raise_errorf ~loc "[%%import]: cannot locate %s in the signature %s"
              field (string_of_lid parent_id)
  in
  loop sig_items

let get_type_decl =
  get_sig_item (fun elem ->
    function
    | Sig_type (id, type_decl, _) when Ident.name id = elem -> Some type_decl
    | _ -> None)

let get_modtype_decl =
  get_sig_item (fun elem ->
    function
    | Sig_modtype (id, type_decl) when Ident.name id = elem -> Some type_decl
    | _ -> None)

let rec longident_of_path path =
  match path with
  | Path.Pident id -> Lident (Ident.name id)
  | Path.Pdot (path, name, _) -> Ldot (longident_of_path path, name)
  | Path.Papply (lhs, rhs) -> Lapply (longident_of_path lhs, longident_of_path rhs)

let rec core_type_of_type_expr ~subst type_expr =
  match type_expr.desc with
  | Tvar None -> Typ.any ()
  | Tvar (Some var) ->
    begin match List.assoc (`Var var) subst with
    | typ -> typ
    | exception Not_found -> Typ.var var
    end
  | Tarrow (label, lhs, rhs, _) ->
    Typ.arrow label (core_type_of_type_expr ~subst lhs)
                    (core_type_of_type_expr ~subst rhs)
  | Ttuple xs ->
    Typ.tuple (List.map (core_type_of_type_expr ~subst) xs)
  | Tconstr (path, args, _) ->
    let lid  = longident_of_path path in
    let args = (List.map (core_type_of_type_expr ~subst) args) in
    begin match List.assoc (`Lid lid) subst with
    | { ptyp_desc = Ptyp_constr (lid, _) } as typ ->
      { typ with ptyp_desc = Ptyp_constr (lid, args) }
    | _ -> assert false
    | exception Not_found ->
      Typ.constr { txt = longident_of_path path; loc = !default_loc } args
    end
  | Tvariant { row_fields; row_closed } ->
    let fields =
      row_fields |> List.map (fun (label, row_field) ->
#if OCAML_VERSION >= (4, 06, 0)
        let label = Location.mknoloc label in
#endif
        match row_field with
        | Rpresent None -> Rtag (label, [], true, [])
        | Rpresent (Some ttyp) ->
          Rtag (label, [], false, [core_type_of_type_expr ~subst ttyp])
        | _ -> assert false)
    in
    Typ.variant fields Closed None
  | _ ->
    assert false

let ptype_decl_of_ttype_decl ~manifest ~subst ptype_name ttype_decl =
  let subst =
    match manifest with
    | Some { ptyp_desc = Ptyp_constr (_, ptype_args); ptyp_loc } ->
      begin try
        subst @ (List.map2 (fun tparam pparam ->
            match tparam with
            | { desc = Tvar (Some var) } -> [`Var var, pparam]
            | { desc = Tvar None }       -> []
            | _ -> assert false)
          ttype_decl.type_params ptype_args
        |> List.concat)
      with Invalid_argument "List.map2" ->
        raise_errorf ~loc:ptyp_loc "Imported type has %d parameter(s), but %d are passed"
                                   (List.length ttype_decl.type_params)
                                   (List.length ptype_args)
      end
    | None -> []
    | _ -> assert false
  in
  let ptype_params =
    List.map2 (fun param variance ->
        core_type_of_type_expr ~subst param,
        (* The equivalent of not specifying the variance explicitly.
           Since the very purpose of ppx_import is to include the full definition,
           it should always be sufficient to rely on the inferencer to deduce variance. *)
        Invariant)
      ttype_decl.type_params ttype_decl.type_variance
  and ptype_kind =
    let map_labels =
      List.map (fun ld ->
        { pld_name       = { txt = Ident.name ld.ld_id; loc = ld.ld_loc };
          pld_mutable    = ld.ld_mutable;
          pld_type       = core_type_of_type_expr ~subst ld.ld_type;
          pld_loc        = ld.ld_loc;
          pld_attributes = ld.ld_attributes; })
    in
    match ttype_decl.type_kind with
    | Type_abstract -> Ptype_abstract
    | Type_open -> Ptype_open
    | Type_record (labels, _) ->
      Ptype_record (map_labels labels)
    | Type_variant constrs ->
      let map_args =
        function
        | Cstr_tuple(args)    ->
          Pcstr_tuple(List.map (core_type_of_type_expr ~subst) args)
#if OCAML_VERSION >= (4, 03, 0)
        | Cstr_record(labels) ->
          Pcstr_record(map_labels labels)
#endif
      in
      Ptype_variant (constrs |> List.map (fun cd ->
        { pcd_name       = { txt = Ident.name cd.cd_id; loc = cd.cd_loc };
          pcd_args       = map_args cd.cd_args;
          pcd_res        = (match cd.cd_res with Some x -> Some (core_type_of_type_expr ~subst x)
                                               | None -> None);
          pcd_loc        = cd.cd_loc;
          pcd_attributes = cd.cd_attributes; }))
  and ptype_manifest =
    match ttype_decl.type_manifest with
    | Some typ -> Some (core_type_of_type_expr ~subst typ)
    | None -> manifest
  in
  { ptype_name; ptype_params; ptype_kind; ptype_manifest;
    ptype_cstrs      = [];
    ptype_private    = ttype_decl.type_private;
    ptype_attributes = ttype_decl.type_attributes;
    ptype_loc        = ttype_decl.type_loc; }

let subst_of_manifest { ptyp_attributes; ptyp_loc } =
  let rec subst_of_expr expr =
    match expr with
    | [%expr [%e? { pexp_desc = Pexp_ident ({ txt = src }) }] :=
             [%e? { pexp_desc = Pexp_ident (dst); pexp_attributes; pexp_loc }]] ->
      [`Lid src, { ptyp_loc = pexp_loc; ptyp_attributes = pexp_attributes;
                   ptyp_desc = Ptyp_constr (dst, []) }]
    | [%expr [%e? { pexp_desc = Pexp_ident ({ txt = src }) }] :=
             [%e? { pexp_desc = Pexp_ident (dst); pexp_attributes; pexp_loc }]; [%e? rest]] ->
      (`Lid src, { ptyp_loc = pexp_loc; ptyp_attributes = pexp_attributes;
                   ptyp_desc = Ptyp_constr (dst, []) }) :: subst_of_expr rest
    | { pexp_loc } ->
      raise_errorf ~loc:pexp_loc "Invalid [@with] syntax"
  in
  match Ast_convenience.find_attr "with" ptyp_attributes with
  | None -> []
  | Some (PStr [{ pstr_desc = Pstr_eval (expr, []) }]) ->
    subst_of_expr expr
  | Some _ ->
    raise_errorf ~loc:ptyp_loc "Invalid [@with] syntax"

let is_self_reference lid =
  let fn = !Location.input_name
           |> Filename.basename
           |> Filename.chop_extension
           |> String.uncapitalize
  in
  match lid with
  | Ldot (_) ->
    let mn = Longident.flatten lid |> List.hd |> String.uncapitalize
    in fn = mn
  | _ -> false

let type_declaration mapper type_decl =
  match type_decl with
  | { ptype_attributes; ptype_name; ptype_manifest = Some {
        ptyp_desc = Ptyp_extension ({ txt = "import"; loc }, payload) } } ->
    begin match payload with
    | PTyp ({ ptyp_desc = Ptyp_constr ({ txt = lid; loc }, _) } as manifest) ->
      if Ast_mapper.tool_name () = "ocamldep" then
        (* Just put it as manifest *)
        if is_self_reference lid then
          { type_decl with ptype_manifest = None }
        else
          { type_decl with ptype_manifest = Some manifest }
      else
        with_default_loc loc (fun () ->
          let ttype_decl = match lid with
            | Lapply _ ->
              raise_errorf ~loc
                "[%%import] cannot import a functor application %s"
                (string_of_lid lid)
            | Lident _ as head_id ->
              let env = Lazy.force lazy_env in
              (* In this case, we know for sure that the user intends this lident
                 as a type name, so we use Typetexp.find_type and let the failure
                 cases propagate to the user. *)
              Typetexp.find_type env loc head_id |> snd
            | Ldot (parent_id, field) ->
              let sig_items = find_sig ~loc parent_id in
              get_type_decl ~loc sig_items parent_id field
          in
          let m, s = if is_self_reference lid then
              None, []
          else begin
            let subst = subst_of_manifest manifest in
            let subst = subst @ [
                `Lid (Lident (Longident.last lid)),
                Typ.constr { txt = Lident ptype_name.txt; loc = ptype_name.loc } []
              ] in
            Some manifest, subst
          end
          in
          let ptype_decl = ptype_decl_of_ttype_decl ~manifest:m ~subst:s ptype_name ttype_decl in
          { ptype_decl with ptype_attributes })
    | _ -> raise_errorf ~loc "Invalid [%%import] syntax"
    end
  | _ -> default_mapper.type_declaration mapper type_decl

let rec psig_of_tsig ~subst ?(trec=[]) tsig =
  match tsig with
  | (Sig_type (_, _, Trec_first) | _) :: _ when trec <> [] ->
#if OCAML_VERSION < (4, 03, 0)
    let psig_desc = Psig_type trec in
#else
    let psig_desc = Psig_type(Recursive, trec) in
#endif
    { psig_desc; psig_loc = Location.none } :: psig_of_tsig ~subst tsig
  | Sig_type (id, ttype_decl, rec_flag) :: rest ->
    let ptype_decl = ptype_decl_of_ttype_decl ~manifest:None ~subst (Location.mknoloc (Ident.name id)) ttype_decl in
    begin match rec_flag with
    | Trec_not ->
#if OCAML_VERSION < (4, 03, 0)
      let psig_desc = Psig_type [ptype_decl] in
#else
      let psig_desc = Psig_type(Nonrecursive, [ptype_decl]) in
#endif
      { psig_desc; psig_loc = Location.none } :: psig_of_tsig ~subst rest
    | Trec_first | Trec_next ->
      psig_of_tsig ~subst ~trec:(ptype_decl :: trec) rest
    end
  | Sig_value (id, { val_type; val_kind; val_loc; val_attributes }) :: rest ->
    let pval_prim =
      match val_kind with
      | Val_reg -> []
#if OCAML_VERSION < (4, 03, 0)
      | Val_prim p -> Primitive.description_list p
#else
      | Val_prim p ->
        let oval = Outcometree.{ oval_name = ""; oval_type = Otyp_abstract;
                                 oval_prims = []; oval_attributes = [] } in
        let oval = Primitive.print p oval in
        oval.Outcometree.oval_prims
#endif
      | _ -> assert false
    in
    { psig_desc = Psig_value {
        pval_name = Location.mknoloc (Ident.name id); pval_loc = val_loc;
        pval_attributes = val_attributes;
        pval_prim; pval_type = core_type_of_type_expr ~subst val_type; };
      psig_loc = val_loc } ::
    psig_of_tsig ~subst rest
  | [] -> []
  | _ -> assert false

let module_type mapper modtype_decl =
  match modtype_decl with
  | { pmty_attributes; pmty_desc = Pmty_extension ({ txt = "import"; loc }, payload) } ->
    begin match payload with
    | PTyp ({ ptyp_desc = Ptyp_package({ txt = lid; loc } as alias, subst) }) ->
      if Ast_mapper.tool_name () = "ocamldep" then
        if is_self_reference lid then
          (* Create a dummy module type to break the circular dependency *)
          { modtype_decl with pmty_desc = Pmty_signature [] }
        else
          (* Just put it as alias *)
          { modtype_decl with pmty_desc = Pmty_alias alias }
      else
        with_default_loc loc (fun () ->
          let env = Lazy.force lazy_env in
          let tmodtype_decl = match lid with
            | Lapply _ ->
              raise_errorf ~loc
                "[%%import] cannot import a functor application %s"
                (string_of_lid lid)
            | Lident _ as head_id ->
              (* In this case, we know for sure that the user intends this lident
                 as a module type name, so we use Typetexp.find_type and
                 let the failure cases propagate to the user. *)
              Typetexp.find_modtype env loc head_id |> snd
            | Ldot (parent_id, field) ->
              let sig_items = find_sig ~loc parent_id in
              get_modtype_decl ~loc sig_items parent_id field
          in
          let sig_items = open_modtype_decl env loc lid tmodtype_decl in
          let subst = List.map (fun ({ txt; }, typ) -> `Lid txt, typ) subst in
          let psig  = psig_of_tsig ~subst sig_items in
          { modtype_decl with pmty_desc = Pmty_signature psig })
    | _ -> raise_errorf ~loc "Invalid [%%import] syntax"
    end
  | _ -> default_mapper.module_type mapper modtype_decl

let () =
  Ast_mapper.register "ppx_import" (fun argv ->
    { default_mapper with type_declaration; module_type; })
