open! Base
open! Stdio
open Loc
open Syntaxtree
open Syntax
open Err
open Names
open Mpst

let set_filename (fname : string) (lexbuf : Lexing.lexbuf) =
  lexbuf.Lexing.lex_curr_p <-
    {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname= fname} ;
  lexbuf

let parse_from_lexbuf lexbuf : scr_module =
  try Syntaxtree.Parser.doc Lexer.token lexbuf with
  | Lexer.LexError msg -> uerr (LexerError msg)
  | Parser.Error ->
      let err_interval =
        (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)
      in
      uerr (ParserError (build err_interval))
  | Err.UserError e -> uerr e
  | e -> Err.violation ("Found a problem:" ^ Exn.to_string e)

let parse fname (ch : In_channel.t) : scr_module =
  let lexbuf = set_filename fname (Lexing.from_channel ch) in
  parse_from_lexbuf lexbuf

let parse_string string = parse_from_lexbuf @@ Lexing.from_string string

let validate_protocols_exn (ast : scr_module) : unit =
  let show ~f ?(sep = "\n") xs =
    (* only show if verbose is on *)
    if Pragma.verbose () then
      String.concat ~sep (List.map ~f xs) |> print_endline
    else ()
  in
  let protocols = ast.protocols in
  let protocols =
    List.map ~f:(Protocol.expand_global_protocol ast) protocols
  in
  show ~f:show_global_protocol protocols ;
  let g_types =
    List.map ~f:(fun p -> (Gtype.of_protocol p, p.value.roles)) protocols
  in
  (* let g_types = List.map ~f:(fun (g, roles) -> (Gtype.normalise g, roles))
     g_types in *)
  show ~f:(fun (g, _) -> Gtype.show g) g_types ;
  if Pragma.refinement_type_enabled () then
    List.iter ~f:(fun (g, _) -> Gtype.validate_refinements_exn g) g_types ;
  if not @@ Pragma.check_directed_choice_disabled () then 
    let l_types =
      List.map
        ~f:(fun (g, roles) ->
          List.map ~f:(fun r -> Ltype.project (RoleName.of_name r) g) roles )
        g_types
    in
    show
      ~f:(fun ls -> String.concat ~sep:"\n" (List.map ~f:Ltype.show ls))
      l_types ;
    let efsmss = List.map ~f:(List.map ~f:Efsm.of_local_type) l_types in
    show
      ~f:(fun efsms ->
        String.concat ~sep:"\n" (List.map ~f:(fun (_, g) -> Efsm.show g) efsms)
        )
      efsmss

let validate_nested_protocols (ast : scr_module) =
  let show ~f ~sep input =
    if Pragma.verbose () then
      print_endline (Printf.sprintf "%s%s" (f input) sep)
    else ()
  in
  Protocol.validate_calls_in_protocols ast ;
  let ast = Protocol.rename_nested_protocols ast in
  show ~f:show_scr_module ~sep:"\n---------\n\n" ast ;
  let global_t = Gtype.global_t_of_module ast in
  show ~f:Gtype.show_global_t ~sep:"\n---------\n\n" global_t ;
  let local_t = Ltype.project_global_t global_t in
  show ~f:Ltype.show_local_t ~sep:"\n" local_t ;
  ()

let validate_exn (ast : scr_module) : unit =
  if Pragma.nested_protocol_enabled () then validate_nested_protocols ast
  else (
    Protocol.ensure_no_nested_protocols ast ;
    validate_protocols_exn ast )

let enumerate_protocols (ast : scr_module) :
    (ProtocolName.t * RoleName.t) list =
  let protocols = ast.protocols in
  let roles p =
    let {value= {name; roles; _}; _} = p in
    List.map
      ~f:(fun role -> (ProtocolName.of_name name, RoleName.of_name role))
      roles
  in
  List.concat_map ~f:(fun p -> roles p) protocols

let enumerate_nested_protocols (ast : scr_module) :
    (ProtocolName.t * RoleName.t) list =
  let global_t = Gtype.global_t_of_module ast in
  let enumerated =
    Map.mapi global_t ~f:(fun ~key:protocol ~data:((roles, roles'), _, _) ->
        List.map (roles @ roles') ~f:(fun role -> (protocol, role)) )
  in
  List.concat @@ Map.data enumerated

let enumerate (ast : scr_module) : (ProtocolName.t * RoleName.t) list =
  if Pragma.nested_protocol_enabled () then enumerate_nested_protocols ast
  else enumerate_protocols ast

let get_global_type ast ~protocol : Gtype.t =
  let gp =
    match
      List.find
        ~f:(fun gt ->
          ProtocolName.equal (ProtocolName.of_name gt.value.name) protocol )
        ast.protocols
    with
    | Some gp -> gp
    | None -> uerr (ProtocolNotFound protocol)
  in
  Protocol.expand_global_protocol ast gp |> Gtype.of_protocol

let project_protocol_role ast ~protocol ~role : Ltype.t =
  get_global_type ast ~protocol |> Ltype.project role

let project_nested_protocol ast ~protocol ~role : Ltype.t =
  let global_t = Gtype.global_t_of_module ast in
  let local_t = Ltype.project_global_t global_t in
  let local_protocol_id = Ltype.LocalProtocolId.create protocol role in
  let _, l_type = Map.find_exn local_t local_protocol_id in
  l_type

let project_role ast ~protocol ~role : Ltype.t =
  if Pragma.nested_protocol_enabled () then
    project_nested_protocol ast ~protocol ~role
  else project_protocol_role ast ~protocol ~role

let generate_fsm ast ~protocol ~role =
  let lt = project_role ast ~protocol ~role in
  Efsm.of_local_type lt

let generate_go_code = Codegen.Go.generate_go_code

let generate_chor_automata ast ~protocol ~role ~server =
  let gp =
    match
      List.find
        ~f:(fun gt ->
          ProtocolName.equal (ProtocolName.of_name gt.value.name) protocol)
        ast.protocols
    with
    | Some gp -> gp
    | None -> uerr (ProtocolNotFound protocol)
  in
  let _ = server in
  let gp = Protocol.expand_global_protocol ast gp in
  let all_roles = List.map ~f:RoleName.of_name gp.value.roles in
  let gt = Gtype.of_protocol gp in
  Chorautomata.of_global_type gt all_roles role

let generate_ocaml_code ~monad ast ~protocol ~role =
  let fsm = generate_fsm ast ~protocol ~role in
  Codegen.Ocaml.gen_code ~monad (protocol, role) fsm

let generate_sexp ast ~protocol =
  let gp =
    match
      List.find
        ~f:(fun gt ->
          ProtocolName.equal (ProtocolName.of_name gt.value.name) protocol )
        ast.protocols
    with
    | Some gp -> gp
    | None -> uerr (ProtocolNotFound protocol)
  in
  let gp = Protocol.expand_global_protocol ast gp in
  let gtype = Gtype.of_protocol gp in
  let gtype = Gtype.normalise gtype in
  Sexp.to_string_hum (Gtype.sexp_of_t gtype)

let generate_ast ~monad ast ~protocol ~role =
  let fsm = generate_fsm ast ~protocol ~role in
  Codegen.Ocaml.gen_ast ~monad (protocol, role) fsm

let generate_fstar_code ast ~protocol ~role =
  let lt = project_role ast ~protocol ~role in
  let efsm = Efsm.of_local_type_with_rec_var_info lt in
  Codegen.Fstar.gen_code efsm
