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
module AbductiveDomain = PulseAbductiveDomain
module LatentIssue = PulseLatentIssue

type t =
  | AbortProgram of AbductiveDomain.t
  | ContinueProgram of AbductiveDomain.t
  | ExitProgram of AbductiveDomain.t
  | LatentAbortProgram of {astate: AbductiveDomain.t; latent_issue: LatentIssue.t}

let continue astate = ContinueProgram astate

let mk_initial pdesc = ContinueProgram (AbductiveDomain.mk_initial pdesc)

let leq ~lhs ~rhs =
  match (lhs, rhs) with
  | AbortProgram astate1, AbortProgram astate2
  | ContinueProgram astate1, ContinueProgram astate2
  | ExitProgram astate1, ExitProgram astate2 ->
      AbductiveDomain.leq ~lhs:astate1 ~rhs:astate2
  | ( LatentAbortProgram {astate= astate1; latent_issue= issue1}
    , LatentAbortProgram {astate= astate2; latent_issue= issue2} ) ->
      LatentIssue.equal issue1 issue2 && AbductiveDomain.leq ~lhs:astate1 ~rhs:astate2
  | _ ->
      false


let pp fmt = function
  | ContinueProgram astate ->
      AbductiveDomain.pp fmt astate
  | ExitProgram astate ->
      F.fprintf fmt "{ExitProgram %a}" AbductiveDomain.pp astate
  | AbortProgram astate ->
      F.fprintf fmt "{AbortProgram %a}" AbductiveDomain.pp astate
  | LatentAbortProgram {astate; latent_issue} ->
      let diagnostic = LatentIssue.to_diagnostic latent_issue in
      let message = Diagnostic.get_message diagnostic in
      let location = Diagnostic.get_location diagnostic in
      F.fprintf fmt "{LatentAbortProgram(%a: %s) %a}" Location.pp location message
        AbductiveDomain.pp astate


let map ~f exec_state =
  match exec_state with
  | AbortProgram astate ->
      AbortProgram (f astate)
  | ContinueProgram astate ->
      ContinueProgram (f astate)
  | ExitProgram astate ->
      ExitProgram (f astate)
  | LatentAbortProgram {astate; latent_issue} ->
      LatentAbortProgram {astate= f astate; latent_issue}


let of_posts pdesc posts =
  List.filter_mapi posts ~f:(fun i exec_state ->
      let ( AbortProgram astate
          | ContinueProgram astate
          | ExitProgram astate
          | LatentAbortProgram {astate} ) =
        exec_state
      in
      L.d_printfln "Creating spec out of state #%d:@\n%a" i pp exec_state ;
      let astate, is_unsat = PulseArithmetic.is_unsat_expensive astate in
      if is_unsat then None
      else
        Some
          (map exec_state ~f:(fun _astate ->
               (* prefer [astate] since it is an equivalent state that has been normalized *)
               AbductiveDomain.of_post pdesc astate )) )
