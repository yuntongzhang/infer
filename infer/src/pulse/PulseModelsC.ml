(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
open PulseBasicInterface
open PulseDomainInterface
open PulseOperations.Import
open PulseModelsImport
module L = Logging

let free deleted_access : model = Basic.free_or_delete `Free CFree deleted_access

let alloc_common allocator ~size_exp_opt : model =
 fun ({path; callee_procname; location; ret= ret_id, _} as model_data) astate ->
  let ret_addr = AbstractValue.mk_fresh () in
  let astate_alloc =
    let continue astate = ContinueProgram astate in
    Basic.alloc_not_null allocator ~initialize:false size_exp_opt model_data astate >>| continue
  in
  let result_null =
    let ret_null_hist =
      Hist.single_call path location (Procname.to_string callee_procname) ~more:"(null case)"
    in
    let ret_null_value = (ret_addr, ret_null_hist) in
    let+ astate_null =
      PulseOperations.write_id ret_id ret_null_value astate
      |> PulseArithmetic.and_eq_int ret_addr IntLit.zero
      >>= PulseOperations.invalidate path
            (StackAddress (Var.of_id ret_id, ret_null_hist))
            location (ConstantDereference IntLit.zero) ret_null_value
    in
    (* L.debug_dev "null branch state: %a\n" AbductiveDomain.pp astate_null; *)
    ContinueProgram astate_null
  in
  [astate_alloc; result_null]


let alloc_not_null_common allocator ~size_exp_opt : model =
 fun model_data astate ->
  let<+> astate = Basic.alloc_not_null ~initialize:false allocator size_exp_opt model_data astate in
  astate


let malloc size_exp = alloc_common CMalloc ~size_exp_opt:(Some size_exp)

let malloc_not_null size_exp = alloc_not_null_common CMalloc ~size_exp_opt:(Some size_exp)

let custom_malloc size_exp model_data astate =
  alloc_common (CustomMalloc model_data.callee_procname) ~size_exp_opt:(Some size_exp) model_data
    astate


let custom_alloc_not_null model_data astate =
  alloc_not_null_common (CustomMalloc model_data.callee_procname) ~size_exp_opt:None model_data
    astate


let realloc_common allocator pointer size : model =
 fun data astate ->
  free pointer data astate
  |> List.concat_map ~f:(fun result ->
         let<*> exec_state = result in
         match (exec_state : ExecutionDomain.t) with
         | ContinueProgram astate ->
             alloc_common allocator ~size_exp_opt:(Some size) data astate
         | ExceptionRaised _
         | ExitProgram _
         | AbortProgram _
         | LatentAbortProgram _
         | LatentInvalidAccess _
         | ISLLatentMemoryError _ ->
             [Ok exec_state] )


let realloc = realloc_common CRealloc


let calloc _n size =
  let ikind = Typ.IUInt in
  let size_expr = Exp.BinOp (Binop.Mult (Some ikind), _n, size) in
  alloc_common CCalloc ~size_exp_opt:(Some size_expr)


let custom_realloc pointer size data astate =
  realloc_common (CustomRealloc data.callee_procname) pointer size data astate


(** TODO: by right, this should check for read on the argument first. *)
let strdup _ : model =
  alloc_common CMalloc ~size_exp_opt:None


let c_mem_single_access_common (dest_addr, dest_hist) access_mode ~desc : model =
  fun {path; location; ret= ret_id, _} astate ->
    let event = Hist.call_event path location desc in
    let updated_hist = Hist.add_event path event dest_hist in
    let ret_val = (dest_addr, updated_hist) in
    let astate = PulseOperations.write_id ret_id ret_val astate in
    PulseOperations.check_and_abduce_addr_access_isl path access_mode location (dest_addr, updated_hist) ~null_noop:false astate
    |> List.map ~f:(fun result ->
      let+ astate = result in
      ContinueProgram astate )


let strlen (dest_addr, dest_hist) : model =
  c_mem_single_access_common (dest_addr, dest_hist) Read ~desc:"strlen()"


let memset (dest_addr, dest_hist) : model =
  c_mem_single_access_common (dest_addr, dest_hist) Write ~desc:"memset()"


let strcpy (dest_addr, dest_hist) _ : model =
  c_mem_single_access_common (dest_addr, dest_hist) Write ~desc:"strcpy()"


let strncpy (dest_addr, dest_hist) (src_addr, src_hist) _ : model =
  strcpy (dest_addr, dest_hist) (src_addr, src_hist)

let access_second_arg _ (addr, hist) : model =
  c_mem_single_access_common (addr, hist) Read ~desc:"other func that uses the second arg"

let access_third_arg _ _ (addr, hist) : model =
  c_mem_single_access_common (addr, hist) Read ~desc:"other func that uses the third arg"

let matchers : matcher list =
  let open ProcnameDispatcher.Call in
  let match_regexp_opt r_opt (_tenv, proc_name) _ =
    Option.exists r_opt ~f:(fun r ->
        let s = Procname.to_string proc_name in
        Str.string_match r s 0 )
  in
  let map_context_tenv f (x, _) = f x in
  [ +BuiltinDecl.(match_builtin free) <>$ capt_arg $--> free
  ; +match_regexp_opt Config.pulse_model_free_pattern <>$ capt_arg $+...$--> free
  ; +BuiltinDecl.(match_builtin malloc) <>$ capt_exp $--> malloc
  ; +match_regexp_opt Config.pulse_model_malloc_pattern <>$ capt_exp $+...$--> custom_malloc
  ; -"realloc" <>$ capt_arg $+ capt_exp $--> realloc
  ; +match_regexp_opt Config.pulse_model_realloc_pattern
    <>$ capt_arg $+ capt_exp $+...$--> custom_realloc
  ; -"calloc" <>$ capt_exp $+ capt_exp $--> calloc
  ; -"strdup" <>$ capt_exp $--> strdup
  ; -"strlen" <>$ capt_arg_payload $+...$--> strlen
  ; -"memset" <>$ capt_arg_payload $+...$--> memset
  ; -"strcpy" <>$ capt_arg_payload $+ capt_arg_payload $+...$--> strcpy
  ; -"strchr" <>$ capt_arg_payload $+ capt_arg_payload $+...$--> strcpy
  ; -"strncpy" <>$ capt_arg_payload $+ capt_arg_payload $+ capt_exp $+...$--> strncpy
  ; -"memcpy" <>$ capt_arg_payload $+ capt_arg_payload $+ capt_exp $+...$--> strncpy
  ; -"memmove" <>$ capt_arg_payload $+ capt_arg_payload $+ capt_exp $+...$--> strncpy
  (** Added for detecting the UAF/DF bugs in the SAVER benchmark. *)
  ; -"grub_xasprintf" <>$ capt_arg_payload $+ capt_arg_payload $+...$--> access_second_arg
  ; -"LXC_ERROR" <>$ capt_arg_payload $+ capt_arg_payload $+ capt_arg_payload $+...$--> access_third_arg
  ; +map_context_tenv PatternMatch.ObjectiveC.is_core_graphics_create_or_copy
    &--> custom_alloc_not_null
  ; +map_context_tenv PatternMatch.ObjectiveC.is_core_foundation_create_or_copy
    &--> custom_alloc_not_null
  ; +BuiltinDecl.(match_builtin malloc_no_fail) <>$ capt_exp $--> malloc_not_null
  ; +match_regexp_opt Config.pulse_model_alloc_pattern &--> custom_alloc_not_null ]
