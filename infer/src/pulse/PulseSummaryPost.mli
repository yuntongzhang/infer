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

val from_lists_of_states_and_summaries : 
        (AbductiveDomain.t option) list
    ->  (AbductiveDomain.summary ExecutionDomain.base_t * label) option list
    ->  t
