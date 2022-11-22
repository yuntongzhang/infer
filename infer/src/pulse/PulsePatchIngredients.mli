open! IStd
module F = Format
module L = Logging
module AbstractValue = PulseAbstractValue
module PathCondition = PulsePathCondition
module AbductiveDomain = PulseAbductiveDomain
module BaseDomain = PulseBaseDomain

open PulseBasicInterface

module AddressHistory : sig
    type t = AbstractValue.t * ValueHistory.t [@@deriving compare, equal]

    val pp : F.formatter -> AbstractValue.t * ValueHistory.t -> unit
end

module VarAddrs : sig
    include PrettyPrintable.MonoMap with type key = Var.t and type value = AddressHistory.t 
end

(* module VarAddrs = PrettyPrintable.MakePPMonoMap (Var) (AddressHistory) *)

type t = 
  { var_addr_map: VarAddrs.t   (** Map from stack var to address + history. *)
  ; reachable_addrs : AbstractValue.Set.t   (** All reachble addrs, traced from stack. *)
  ; 

  }

val build_from_astate : AbductiveDomain.t -> t
