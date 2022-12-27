open! IStd
module F = Format
module L = Logging
open PulseBasicInterface
open PulseDomainInterface

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

type summary_post = (label * (AbductiveDomain.t option)) [@@deriving yojson_of]

type t = summary_post list [@@deriving yojson_of]

(* From (unfiltered) post-state, and computed summary with label, construct a
   structure for dumping information. *)
let construct_summary_post (astate : AbductiveDomain.t option) (summary_label : (AbductiveDomain.summary ExecutionDomain.base_t * label) option) =
  match summary_label with
    | None -> (ErrorException, None) (* None summary means exception happened*)
    | Some (_, label) -> (label, astate)


let from_lists_of_states_and_summaries states summary_labels =
  let result_list = List.map2 states summary_labels ~f:construct_summary_post in
  match result_list with
    | Ok result -> result
    | Unequal_lengths -> [] (* error case with unequal legnth between the two *)
