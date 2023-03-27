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

type summary_post = (label * (ExecutionDomain.summary) option) [@@deriving yojson_of]

type t = summary_post list [@@deriving yojson_of]

val from_lists_of_summaries : 
    (AbductiveDomain.summary ExecutionDomain.base_t * label) option list
    ->  t
