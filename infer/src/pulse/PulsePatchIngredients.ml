open! IStd
module F = Format
module L = Logging
module AbstractValue = PulseAbstractValue
module PathCondition = PulsePathCondition
module AbductiveDomain = PulseAbductiveDomain
module BaseDomain = PulseBaseDomain

open PulseBasicInterface

module AbstractValues = struct
  type t = AbstractValue.t list

  let pp f values = 
    F.fprintf f "[" ;
    List.iter values ~f:(AbstractValue.pp f) ;
    F.fprintf f "[" ;
end

module AddressHistory = struct
  type t = AbstractValue.t * ValueHistory.t [@@deriving compare, equal]
  
  let pp f (addr, history) = 
    AbstractValue.pp f addr ;
    F.fprintf f " - " ;
    ValueHistory.pp f history ;
end

module VarAddrs = PrettyPrintable.MakePPMonoMap (Var) (AddressHistory)

type t = 
  { var_addr_map: VarAddrs.t   (** Map from stack var to address + history. *)
  ; reachable_addrs : AbstractValue.Set.t   (** All reachble addrs, traced from stack. *)
  ; 

  }


let build_from_astate ({ post } : AbductiveDomain.t) = 
  let ({ attrs } as post_domain) = (post :> BaseDomain.t) in 
  let var_addr_triples = BaseDomain.extract_stack_var_triples post_domain in
  (* let var_addr_pairs = BaseDomain.extract_stack_var_addr_pairs post_domain in *)
  (** Map from stack var to address + history. *)
  let convert_pairs_to_map triples = 
    List.fold ~init:VarAddrs.empty triples ~f:(fun old_map (var, addr, history) ->
        match VarAddrs.find_opt var old_map with
        | None           -> VarAddrs.add var (addr, history) old_map 
        | Some (_, old_history) -> (* Only keep the one with latest timestamp *)
          let compare_res = ValueHistory.compare_timestamp old_history history in
          if compare_res >= 0 then 
            (* old history is more recent *)
            old_map
          else
            VarAddrs.add var (addr, history) old_map
      )
    in
  let var_addr_map = convert_pairs_to_map var_addr_triples in
  (** All reachble addrs, traced from stack. *)
  let extract_addrs_from_map map = 
    VarAddrs.fold (fun _ (addr, _) acc -> addr::acc) map []
    in  
  let stack_addrs = extract_addrs_from_map var_addr_map in
  let reachable_addrs = BaseDomain.reachable_addresses_from (Caml.List.to_seq stack_addrs) post_domain in
  {var_addr_map; reachable_addrs} 


