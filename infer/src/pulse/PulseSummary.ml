(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module F = Format
module L = Logging
open PulseBasicInterface
open PulseDomainInterface
open PulseOperationResult.Import
module SummaryPost = PulseSummaryPost

type t = ExecutionDomain.summary list [@@deriving yojson_of]

let pp fmt pre_posts =
  F.open_vbox 0 ;
  F.fprintf fmt "%d pre/post(s)@;" (List.length pre_posts) ;
  List.iteri pre_posts ~f:(fun i (pre_post : ExecutionDomain.summary) ->
      F.fprintf fmt "#%d: @[%a@]@;" i ExecutionDomain.pp_summary pre_post ) ;
  F.close_box ()


let exec_summary_of_post_common tenv ~continue_program ~exception_raised proc_desc err_log location
    (exec_astate : ExecutionDomain.t) : (_ ExecutionDomain.base_t * SummaryPost.label) SatUnsat.t =
  let summarize (astate : AbductiveDomain.t)
      ~(exec_domain_of_summary : AbductiveDomain.Summary.summary -> 'a ExecutionDomain.base_t) :
      _ ExecutionDomain.base_t SatUnsat.t =
    let open SatUnsat.Import in
    let+ summary_result =
      AbductiveDomain.Summary.of_post tenv
        (Procdesc.get_proc_name proc_desc)
        (Procdesc.get_attributes proc_desc)
        location astate
    in
    match (summary_result : _ result) with
    | Ok summary ->
        exec_domain_of_summary summary, SummaryPost.Ok
    | Error (`RetainCycle (summary, astate, assignment_traces, value, path, location)) ->
        let real_summary = PulseReport.report_summary_error tenv proc_desc err_log
          ( ReportableError
              {astate; diagnostic= RetainCycle {assignment_traces; value; path; location}}
          , summary )
        |> Option.value ~default:(exec_domain_of_summary summary)
    in real_summary, SummaryPost.ErrorRetainCycle
    | Error (`MemoryLeak (summary, astate, allocator, allocation_trace, location)) ->
        let real_summary = PulseReport.report_summary_error tenv proc_desc err_log
          ( ReportableError {astate; diagnostic= MemoryLeak {allocator; allocation_trace; location}}
          , summary )
        |> Option.value ~default:(exec_domain_of_summary summary)
    in real_summary, SummaryPost.ErrorMemoryLeak
    | Error (`JavaResourceLeak (summary, astate, class_name, allocation_trace, location)) ->
        let real_summary = PulseReport.report_summary_error tenv proc_desc err_log
          ( ReportableError
              {astate; diagnostic= JavaResourceLeak {class_name; allocation_trace; location}}
          , summary )
        |> Option.value ~default:(exec_domain_of_summary summary)
    in real_summary, SummaryPost.ErrorResourceLeak
    | Error (`CSharpResourceLeak (summary, astate, class_name, allocation_trace, location)) ->
        let real_summary = PulseReport.report_summary_error tenv proc_desc err_log
          ( ReportableError
              {astate; diagnostic= CSharpResourceLeak {class_name; allocation_trace; location}}
          , summary )
        |> Option.value ~default:(exec_domain_of_summary summary)
    in real_summary, SummaryPost.ErrorResourceLeak
    | Error (`PotentialInvalidAccessSummary (summary, astate, address, must_be_valid)) -> (
      match
        let open IOption.Let_syntax in
        let* addr = DecompilerExpr.abstract_value_of_expr address in
        let* _, attrs = AbductiveDomain.find_post_cell_opt addr (astate :> AbductiveDomain.t) in
        Attributes.get_invalid attrs
      with
      | None ->
          let real_summary = ExecutionDomain.LatentInvalidAccess
            {astate= summary; address; must_be_valid; calling_context= []}
      in real_summary, SummaryPost.LatentInvalidAccess
      | Some (invalidation, invalidation_trace) ->
          (* NOTE: this probably leads to the error being dropped as the access trace is unlikely to
             contain the reason for invalidation and thus we will filter out the report. TODO:
             figure out if that's a problem. *)
          let real_summary = PulseReport.report_summary_error tenv proc_desc err_log
            ( ReportableError
                { diagnostic=
                    AccessToInvalidAddress
                      { calling_context= []
                      ; invalid_address= address
                      ; invalidation
                      ; invalidation_trace
                      ; access_trace= fst must_be_valid
                      ; must_be_valid_reason= snd must_be_valid }
                ; astate }
            , summary )
          |> Option.value ~default:(exec_domain_of_summary summary) 
    in real_summary, SummaryPost.ErrorInvalidAccess ) )
  in
  match exec_astate with
  | ExceptionRaised astate ->
      summarize astate ~exec_domain_of_summary:exception_raised
  | ContinueProgram astate ->
      summarize astate ~exec_domain_of_summary:continue_program
  (* already a summary but need to reconstruct the variants to make the type system happy :( *)
  | AbortProgram astate ->
      Sat (AbortProgram astate, SummaryPost.AbortProgram)
  | ExitProgram astate ->
      Sat (ExitProgram astate, SummaryPost.ExitProgram)
  | LatentAbortProgram {astate; latent_issue} ->
      Sat (LatentAbortProgram {astate; latent_issue}, SummaryPost.LatentAbortProgram)
  | LatentInvalidAccess {astate; address; must_be_valid; calling_context} ->
      Sat (LatentInvalidAccess {astate; address; must_be_valid; calling_context})
        , SummaryPost.LatentInvalidAccess


let force_exit_program tenv proc_desc err_log post =
  let summary_label = exec_summary_of_post_common tenv proc_desc err_log post
    ~continue_program:(fun astate -> ExitProgram astate)
    ~exception_raised:(fun astate -> ExitProgram astate)
  in match summary_label with
    | Unsat -> Unsat
    | Sat inner -> Sat (fst inner)


let write_summary_and_posts_json (posts : ExecutionDomain.t list) summary_labels =
  let ok_states_from_posts = List.map posts ~f:(fun exec_astate ->
    match exec_astate with
    | ContinueProgram astate -> Some astate
    | _                      -> None
  )
  in
  (* Note that, here, ContinueProgram in exec_astate may still have error *)
  let summary_posts = SummaryPost.from_lists_of_states_and_summaries ok_states_from_posts summary_labels in
  let json_summary_posts = [%yojson_of: SummaryPost.t] summary_posts in
  let f_json json_content fname = Yojson.Safe.to_file fname json_content;
    (* Yojson.Safe.to_channel stdout json_content;
    Out_channel.newline stdout;
    Out_channel.flush stdout; *)
  in
  f_json json_summary_posts "summary_posts.json"


let of_posts tenv proc_desc err_log location posts =
  let summary_labels = List.mapi posts ~f:(fun i exec_state ->
      L.d_printfln "Creating spec out of state #%d:@\n%a" i ExecutionDomain.pp exec_state ;
      exec_summary_of_post_common tenv proc_desc err_log location exec_state
        ~continue_program:(fun astate -> ContinueProgram astate)
      |> SatUnsat.sat )
  in
  let () = match Config.pulse_function_only with
    | None -> () (* function-only not specified - assume doing normal error checking *)
    | _ -> write_summary_and_posts_json posts summary_labels
  in
  let filtered_summary_labels = List.filter_map summary_labels ~f:(fun x -> x) in
  List.map filtered_summary_labels ~f:fst


(* let of_posts tenv proc_desc err_log location posts =
  List.filter_mapi posts ~f:(fun i exec_state ->
      L.d_printfln "Creating spec out of state #%d:@\n%a" i ExecutionDomain.pp exec_state ;
      exec_summary_of_post_common tenv proc_desc err_log location exec_state
        ~continue_program:(fun astate -> ContinueProgram astate)
        ~exception_raised:(fun astate -> ExceptionRaised astate)
      |> SatUnsat.sat ) *)


let mk_objc_self_pvar proc_name = Pvar.mk Mangled.self proc_name

let mk_this_pvar proc_name = Pvar.mk Mangled.this proc_name

let find_self proc_name (proc_attrs : ProcAttributes.t) =
  if Procname.is_objc_instance_method proc_name then Some (mk_objc_self_pvar proc_name)
  else if Procname.is_java_instance_method proc_name then Some (mk_this_pvar proc_name)
  else
    match proc_attrs.clang_method_kind with
    | CPP_INSTANCE ->
        Some (mk_this_pvar proc_name)
    | _ ->
        None


let init_fields_zero tenv path location ~zero addr typ astate =
  let get_fields typ =
    match typ.Typ.desc with
    | Tstruct struct_name ->
        Tenv.lookup tenv struct_name |> Option.map ~f:(fun {Struct.fields} -> fields)
    | _ ->
        None
  in
  let rec init_fields_zero_helper addr typ astate =
    match get_fields typ with
    | Some fields ->
        List.fold fields ~init:(Ok astate) ~f:(fun acc (field, field_typ, _) ->
            let* acc in
            let acc, field_addr = Memory.eval_edge addr (FieldAccess field) acc in
            init_fields_zero_helper field_addr field_typ acc )
    | None ->
        PulseOperations.write_deref path location ~ref:addr ~obj:zero astate
  in
  init_fields_zero_helper addr typ astate


(** Constructs summary [{self = 0} {return = self}] when [proc_desc] returns a POD type. This allows
    us to connect invalidation with invalid access in the trace *)
let mk_nil_messaging_summary_aux tenv proc_name (proc_attrs : ProcAttributes.t) =
  let path = PathContext.initial in
  let t0 = path.PathContext.timestamp in
  let self = mk_objc_self_pvar proc_name in
  let astate = AbductiveDomain.mk_initial tenv proc_name proc_attrs in
  let** astate, (self_value, self_history) =
    PulseOperations.eval_deref path proc_attrs.loc (Lvar self) astate
  in
  let** astate = PulseArithmetic.prune_eq_zero self_value astate in
  let event = ValueHistory.NilMessaging (proc_attrs.loc, t0) in
  let updated_self_value_hist = (self_value, ValueHistory.sequence event self_history) in
  match List.last proc_attrs.formals with
  | Some (last_formal, {desc= Tptr (typ, _)}, _) when Mangled.is_return_param last_formal ->
      let ret_param_var = Pvar.get_ret_param_pvar proc_name in
      let** astate, ret_param_var_addr_hist =
        PulseOperations.eval_deref path proc_attrs.loc (Lvar ret_param_var) astate
      in
      Sat
        (init_fields_zero tenv path proc_attrs.loc ~zero:updated_self_value_hist
           ret_param_var_addr_hist typ astate )
  | _ ->
      let ret_var = Pvar.get_ret_pvar proc_name in
      let** astate, ret_var_addr_hist =
        PulseOperations.eval path Write proc_attrs.loc (Lvar ret_var) astate
      in
      Sat
        (PulseOperations.write_deref path proc_attrs.loc ~ref:ret_var_addr_hist
           ~obj:updated_self_value_hist astate )


let mk_latent_non_POD_nil_messaging tenv proc_name (proc_attrs : ProcAttributes.t) =
  let path = PathContext.initial in
  let self = mk_objc_self_pvar proc_name in
  let astate = AbductiveDomain.mk_initial tenv proc_name proc_attrs in
  let** astate, (self_value, _self_history) =
    PulseOperations.eval_deref path proc_attrs.loc (Lvar self) astate
  in
  let trace = Trace.Immediate {location= proc_attrs.loc; history= ValueHistory.epoch} in
  let** astate = PulseArithmetic.prune_eq_zero self_value astate in
  let++ summary =
    let open SatUnsat.Import in
    AbductiveDomain.Summary.of_post tenv proc_name proc_attrs proc_attrs.loc astate
    >>| AccessResult.ignore_leaks >>| AccessResult.of_abductive_summary_result
    >>| AccessResult.with_summary
  in
  ExecutionDomain.LatentInvalidAccess
    { astate= summary
    ; address= Decompiler.find self_value astate
    ; must_be_valid=
        (trace, Some (SelfOfNonPODReturnMethod (ProcAttributes.to_return_type proc_attrs)))
    ; calling_context= [] }


let mk_objc_nil_messaging_summary tenv proc_name (proc_attrs : ProcAttributes.t) =
  if Procname.is_objc_instance_method proc_name then (
    if proc_attrs.is_ret_type_pod then (
      (* In ObjC, when a method is called on nil, there is no NPE, the method is actually not called
         and the return value is 0/false/nil.  We create a nil summary to avoid reporting NPE in
         this case.  However, there is an exception in the case where the return type is non-POD.
         In that case it's UB and we want to report an error. *)
      match
        (let** astate = mk_nil_messaging_summary_aux tenv proc_name proc_attrs in
         let open SatUnsat.Import in
         AbductiveDomain.Summary.of_post tenv proc_name proc_attrs proc_attrs.loc astate
         >>| AccessResult.ignore_leaks >>| AccessResult.of_abductive_summary_result
         >>| AccessResult.with_summary )
        |> PulseOperationResult.sat_ok
      with
      | Some summary ->
          Some (ContinueProgram summary)
      | None ->
          L.internal_error
            "mk_nil_messaging_summary_aux for %a resulted in an error or an unsat state" Procname.pp
            proc_name ;
          None )
    else
      match
        mk_latent_non_POD_nil_messaging tenv proc_name proc_attrs |> PulseOperationResult.sat_ok
      with
      | Some _ as some_summary ->
          some_summary
      | None ->
          L.internal_error
            "mk_latent_non_POD_nil_messaging for %a resulted in an error or an unsat state"
            Procname.pp proc_name ;
          None )
  else None


let positive_allocated_self proc_name location self_address astate =
  (* it's important to do the prune *first* before the dereference to detect contradictions if the
     address is equal to 0 *)
  let set_positive_self =
    if Procname.is_objc_method proc_name then
      (* for objc the method is called only if self>0, so we use prune_positive instead of and_positive*)
      PulseArithmetic.prune_positive
    else PulseArithmetic.and_positive
  in
  set_positive_self (fst self_address) astate
  >>|= PulseOperations.eval_access PathContext.initial Read location self_address Dereference
  >>|| fst


let initial_with_positive_self proc_name (proc_attrs : ProcAttributes.t) initial_astate =
  match find_self proc_name proc_attrs with
  | Some self_var -> (
      let result =
        let** astate, self_address =
          PulseOperations.eval_deref PathContext.initial proc_attrs.loc (Lvar self_var)
            initial_astate
        in
        positive_allocated_self proc_name proc_attrs.loc self_address astate
      in
      match PulseOperationResult.sat_ok result with
      | Some astate ->
          astate
      | None ->
          L.internal_error
            "found an error or an unsat state when adding [self > 0] to %a's initial state %a"
            AbductiveDomain.pp initial_astate Procname.pp proc_name ;
          initial_astate )
  | None ->
      initial_astate


let append_objc_actual_self_positive proc_name (proc_attrs : ProcAttributes.t) self_actual astate =
  match self_actual with
  | Some (self, _) when Procname.is_objc_instance_method proc_name ->
      positive_allocated_self proc_name proc_attrs.loc self astate
  | _ ->
      Sat (Ok astate)
