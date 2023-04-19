open! IStd
module F = Format
module L = Logging
open PulseDomainInterface

type start_end_loc = int * int [@@deriving yojson_of]

type label =
  | Ok of start_end_loc
  | ExitProgram of start_end_loc
  | ErrorRetainCycle of start_end_loc
  | ErrorMemoryLeak of start_end_loc
  | ErrorResourceLeak of start_end_loc
  | AbortProgram of start_end_loc
  | LatentAbortProgram of start_end_loc
  | InvalidAccess of start_end_loc
  | LatentInvalidAccess of start_end_loc
  | ISLLatentMemoryError of start_end_loc
[@@deriving yojson_of]

type summary_post = label * (AbductiveDomain.summary) [@@deriving yojson_of]

type t = summary_post list [@@deriving yojson_of]

(* From the computed summary with label, construct a structure for dumping information. *)
let construct_summary_post (summary_label : AbductiveDomain.summary ExecutionDomain.base_t * label) =
  let summary, label = summary_label in
    (* The meta data in summary is already captured by labels;
        strip those and standardize the format of summary. *)
    match summary with
    | ContinueProgram astate
    | ExceptionRaised astate
    | ExitProgram astate
    | AbortProgram {astate; _; }
    | LatentAbortProgram {astate; _ }
    | LatentInvalidAccess {astate; _; }
    | ISLLatentMemoryError astate ->
      label, astate


let from_lists_of_summaries summary_labels =
  let result_list = List.map summary_labels ~f:construct_summary_post in
  result_list
