open! IStd
module F = Format
module L = Logging
open PulseBasicInterface
open PulseDomainInterface

module ExecutionDomain = PulseExecutionDomain

type label =
  | Ok
  | AbortProgram
  | ExitProgram
  | LatentAbortProgram
  | LatentInvalidAccess
  | ISLLatentMemoryError
  | ErrorRetainCycle
  | ErrorMemoryLeak
  | ErrorResourceLeak
  | ErrorInvalidAccess
  | ErrorException
  | ErrorOthers
[@@deriving yojson_of]

type summary_post = (label * (ExecutionDomain.summary) option) [@@deriving yojson_of]

type t = summary_post list [@@deriving yojson_of]

(* From the computed summary with label, construct a structure for dumping information. *)
let construct_summary_post (summary_label : (AbductiveDomain.summary ExecutionDomain.base_t * label) option) =
  match summary_label with
    | None -> (ErrorException, None) (* None summary means exception happened*)
    | Some (summary, label) -> (label, Some summary)


let from_lists_of_summaries summary_labels =
  let result_list = List.map summary_labels ~f:construct_summary_post in
  result_list
