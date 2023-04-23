(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module F = Format
open PulseBasicInterface
module AbductiveDomain = PulseAbductiveDomain
module Decompiler = PulseAbductiveDecompiler
module Diagnostic = PulseDiagnostic
module LatentIssue = PulseLatentIssue

(* The type variable is needed to distinguish summaries from plain states.

   Some of the variants have summary-typed states instead of plain states, to ensure we have
   normalized them and don't need to normalize them again. *)
type 'abductive_domain_t base_t =
  | ContinueProgram of 'abductive_domain_t
  | ExceptionRaised of 'abductive_domain_t
  | ExitProgram of AbductiveDomain.summary
  | AbortProgram of 
      {astate: AbductiveDomain.summary; error_trace_start: Location.t; error_trace_end: Location.t }
  | LatentAbortProgram of {astate: AbductiveDomain.summary; latent_issue: LatentIssue.t}
  | LatentInvalidAccess of
      { astate: AbductiveDomain.summary
      ; address: Decompiler.expr
      ; must_be_valid: (Trace.t * Invalidation.must_be_valid_reason option[@yojson.opaque])
      ; calling_context: ((CallEvent.t * Location.t) list[@yojson.opaque]) }
  | ISLLatentMemoryError of AbductiveDomain.summary
[@@deriving equal, compare, yojson_of]

type t = AbductiveDomain.t base_t [@@deriving yojson_of]

let continue astate = ContinueProgram astate

let leq ~lhs ~rhs =
  phys_equal lhs rhs
  ||
  match (lhs, rhs) with
  | AbortProgram {astate=astate1}, AbortProgram {astate=astate2}
  | ExitProgram astate1, ExitProgram astate2
  | ISLLatentMemoryError astate1, ISLLatentMemoryError astate2 ->
      AbductiveDomain.leq ~lhs:(astate1 :> AbductiveDomain.t) ~rhs:(astate2 :> AbductiveDomain.t)
  | ExceptionRaised astate1, ExceptionRaised astate2
  | ContinueProgram astate1, ContinueProgram astate2 ->
      AbductiveDomain.leq ~lhs:astate1 ~rhs:astate2
  | ( LatentAbortProgram {astate= astate1; latent_issue= issue1}
    , LatentAbortProgram {astate= astate2; latent_issue= issue2} ) ->
      LatentIssue.equal issue1 issue2
      && AbductiveDomain.leq ~lhs:(astate1 :> AbductiveDomain.t) ~rhs:(astate2 :> AbductiveDomain.t)
  | ( LatentInvalidAccess {astate= astate1; address= v1; must_be_valid= _}
    , LatentInvalidAccess {astate= astate2; address= v2; must_be_valid= _} ) ->
      Decompiler.equal_expr v1 v2
      && AbductiveDomain.leq ~lhs:(astate1 :> AbductiveDomain.t) ~rhs:(astate2 :> AbductiveDomain.t)
  | _ ->
      false


let pp fmt = function
  | AbortProgram {astate} ->
      F.fprintf fmt "{AbortProgram %a}" AbductiveDomain.pp (astate :> AbductiveDomain.t)
  | ContinueProgram astate ->
      AbductiveDomain.pp fmt astate
  | ExceptionRaised astate ->
      F.fprintf fmt "{ExceptionRaised %a}" AbductiveDomain.pp astate
  | ExitProgram astate ->
      F.fprintf fmt "{ExitProgram %a}" AbductiveDomain.pp (astate :> AbductiveDomain.t)
  | ISLLatentMemoryError astate ->
      F.fprintf fmt "{ISLLatentMemoryError %a}" AbductiveDomain.pp (astate :> AbductiveDomain.t)
  | LatentAbortProgram {astate; latent_issue} ->
      let diagnostic = LatentIssue.to_diagnostic latent_issue in
      let message = Diagnostic.get_message diagnostic in
      let location = Diagnostic.get_location diagnostic in
      F.fprintf fmt "{LatentAbortProgram(%a: %s) %a}" Location.pp location message
        AbductiveDomain.pp
        (astate :> AbductiveDomain.t)
  | LatentInvalidAccess {astate; address; must_be_valid= _} ->
      F.fprintf fmt "{LatentInvalidAccess(%a) %a}" Decompiler.pp_expr address AbductiveDomain.pp
        (astate :> AbductiveDomain.t)


(* do not export this function as there lies wickedness: clients should generally care about what
   kind of state they are manipulating so let's not encourage them not to *)
let get_astate : t -> AbductiveDomain.t = function
  | ExceptionRaised astate | ContinueProgram astate ->
      astate
  | ExitProgram astate
  | AbortProgram {astate}
  | LatentAbortProgram {astate}
  | LatentInvalidAccess {astate}
  | ISLLatentMemoryError astate ->
      (astate :> AbductiveDomain.t)


let is_unsat_cheap exec_state = PathCondition.is_unsat_cheap (get_astate exec_state).path_condition

type summary = AbductiveDomain.summary base_t [@@deriving compare, equal, yojson_of]

let equal_fast exec_state1 exec_state2 =
  phys_equal exec_state1 exec_state2
  ||
  match (exec_state1, exec_state2) with
  | AbortProgram {astate=astate1}, AbortProgram {astate=astate2}
  | ExitProgram astate1, ExitProgram astate2
  | ISLLatentMemoryError astate1, ISLLatentMemoryError astate2 ->
      phys_equal astate1 astate2
  | ContinueProgram astate1, ContinueProgram astate2 ->
      phys_equal astate1 astate2
  | _ ->
      false


let is_normal (exec_state : t) : bool =
  match exec_state with ExceptionRaised _ -> false | _ -> true


let is_exceptional (exec_state : t) : bool =
  match exec_state with ExceptionRaised _ -> true | _ -> false


let exceptional_to_normal : t -> t = function
  | ExceptionRaised astate ->
      ContinueProgram astate
  | x ->
      x


(** Do not export this. Update the inner AbductiveDomain without changing anything else. *)
(* let update_astate (exec_state: t) (new_astate: AbductiveDomain.t) : t =
  (* let new_astate_summary = (new_astate :> AbductiveDomain.summary) in
      *)
  let new_astate_summary = new_astate in
  match exec_state with
  | ContinueProgram _ -> ContinueProgram new_astate
  | ExceptionRaised _ -> ExceptionRaised new_astate
  | ExitProgram _ ->     ExitProgram new_astate_summary
  | AbortProgram _ ->    AbortProgram new_astate_summary
  | ISLLatentMemoryError _ -> ISLLatentMemoryError new_astate_summary
  | LatentAbortProgram latent_abort ->
      LatentAbortProgram {latent_abort with astate=new_astate_summary}
  | LatentInvalidAccess latent_invalid_access ->
      LatentInvalidAccess {latent_invalid_access with astate=new_astate_summary} *)


let add_new_trace_loc exec_state location =
  match exec_state with
  | ContinueProgram astate ->
      let new_astate = AbductiveDomain.add_new_trace_loc astate location in
      ContinueProgram new_astate
  | ExceptionRaised astate ->
      let new_astate = AbductiveDomain.add_new_trace_loc astate location in
      ExceptionRaised new_astate
  (** For state where summary is already extracted, there is no need to record exec trace anymore. *)
  | _ -> exec_state
