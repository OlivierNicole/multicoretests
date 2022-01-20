open QCheck

(************************************************************************ *)
(*                       Tests of a simple reference                      *)
(************************************************************************ *)
module Sut =
  struct
    let sut = ref 0
    let get () = !sut
    let set i  = sut:=i
    let add i  = let old = !sut in sut:=i + old (* buggy: not atomic *)
    let incr () = incr sut     (* buggy: not guaranteed to be atomic *)
    let decr () = decr sut     (* buggy: not guaranteed to be atomic *)
end

module RConf = struct
  type t = int ref

  type cmd =
    | Get
    | Set of int
    | Add of int
    | Incr
    | Decr

  let show_cmd = function
    | Get -> "Get"
    | Set i -> Printf.sprintf "Set %i" i
    | Add i -> Printf.sprintf "Add %i" i
    | Incr -> "Incr"
    | Decr -> "Decr"

  let gen_cmd =
    let open Gen in
    frequency
      [1, return Get;
       1, map (fun v -> Set v) small_nat;
       1, map (fun v -> Add v) small_nat;
       1, return Incr;
       1, return Decr;
      ]

  type res = RGet of int | RSet | RAdd | RIncr | RDecr

  let show_res = function
    | RGet i -> Printf.sprintf "RGet %i" i
    | RSet -> "RSet"
    | RAdd -> "RAdd"
    | RIncr -> "RIncr"
    | RDecr -> "RDecr"

  let init () = Sut.sut

  let run c _r = match c with
    | Get   -> RGet (Sut.get ())
    | Set i -> (Sut.set i; RSet)
    | Add i -> (Sut.add i; RAdd)
    | Incr  -> (Sut.incr (); RIncr)
    | Decr  -> (Sut.decr (); RDecr)

  let cleanup _ = Sut.set 0
end

module RT = Lin.Make(RConf)

(*********************************************************************** *)
(*          (Failing) tests of non-atomic array operations               *)
(*********************************************************************** *)

(* Signature of array elements *)
module type Val = sig
  type t
  val init : t
  val show : t -> string
  val gen : t Gen.t
end

module Int : Val = struct
  type t = int
  let init = 0
  let show = string_of_int
  let gen = Gen.nat
end

module Float : Val = struct
  type t = float
  let init = 1.
  let show = string_of_float
  let gen = Gen.float
end

module IntOpt : Val = struct
  type t = int option
  let init = Some 0
  let show =
    let open Printf in function
    | None -> "None"
    | Some i -> sprintf "Some %i" i
  let gen = Gen.opt ~ratio:0.5 Gen.nat
end

module FloatOpt : Val = struct
  type t = float option
  let init = Some 0.
  let show =
    let open Printf in function
    | None -> "None"
    | Some v -> sprintf "Some %f" v
  let gen = Gen.opt ~ratio:0.5 Gen.float
end

(* Signature of array state *)
module type ArraySut = sig
  module Val : Val
  type t
  val sut8 : t
  val get : int -> Val.t
  val set : int -> Val.t -> unit
  val exchange : int -> Val.t -> Val.t
  val cleanup : unit -> unit
end

(* Non-atomic arrays *)
module NAASut (Val : Val) = struct
  module Val = Val
  type t = Val.t array
  let sut = Array.make 8 Val.init
  let sut8 = sut
  let get i = Array.get sut i
  let set i v = Array.set sut i v
  let exchange i v = let old = Array.get sut i in Array.set sut i v; old
  let cleanup () = Array.iteri (fun i _ -> Atomic.Array.set sut i Val.init) sut
end

(* Atomic arrays *)
module AASut (Val : Val) = struct
  module Val = Val
  type t = Val.t array
  let sut = Array.make 8 Val.init
  let sut8 = sut
  let get i = Atomic.Array.get sut i
  let set i v = Atomic.Array.set sut i v
  let exchange i v = Atomic.Array.unsafe_exchange sut i v
  let cleanup () =  Array.iteri (fun i _ -> Array.set sut i Val.init) sut
end

module ArrayConf (Val : Val) (ASut : ArraySut with module Val = Val) = struct
  type t = ASut.t

  type cmd =
    | Get of int_arg
    | Set of int_arg * Val.t
    | Xchg of int_arg * Val.t
  and int_arg = int [@gen Gen.nat]

  let show_cmd =
    let open Printf in function
    | Get i -> sprintf "Get %i" i
    | Set (i,v) -> sprintf "Set (%i, %s)" i (Val.show v)
    | Xchg (i,v) -> sprintf "Xchg (%i, %s)" i (Val.show v)

  let gen_cmd =
    let open Gen in
    frequency
      [1, map (fun i -> Get i) (int_bound 7);
       (*1, map2 (fun i v -> Set (i,v)) (int_bound 7) Val.gen;*)
       1, map2 (fun i v -> Xchg (i,v)) (int_bound 7) Val.gen;
      ]

  type res = RGet of Val.t | RSet | RXchg of Val.t

  let show_res =
    let open Printf in function
    | RGet v -> sprintf "RGet %s" (Val.show v)
    | RSet -> sprintf "RSet"
    | RXchg v -> sprintf "RXchg %s" (Val.show v)

  let init () = ASut.sut8

  let run c _r = match c with
    | Get i -> RGet (ASut.get i)
    | Set (i,v) -> (ASut.set i v; RSet)
    | Xchg (i,v) -> (let newi = ASut.exchange i v in RXchg newi)

  let cleanup _ = ASut.cleanup ()
end

module IntNAAT = Lin.Make(ArrayConf(Int)(NAASut(Int)));;
module FloatNAAT = Lin.Make(ArrayConf(Float)(NAASut(Float)));;
module IntOptNAAT = Lin.Make(ArrayConf(IntOpt)(NAASut(IntOpt)));;
module FloatOptNAAT = Lin.Make(ArrayConf(FloatOpt)(NAASut(FloatOpt)));;
module IntAAT = Lin.Make(ArrayConf(Int)(AASut(Int)));;
module FloatAAT = Lin.Make(ArrayConf(Float)(AASut(Float)));;
module IntOptAAT = Lin.Make(ArrayConf(IntOpt)(AASut(IntOpt)));;
module FloatOptAAT = Lin.Make(ArrayConf(FloatOpt)(AASut(FloatOpt)));;

(*
(** ********************************************************************** *)
(**                   Tests of the Atomic module                           *)
(** ********************************************************************** *)
module AConf =
struct
  type t = int Atomic.t

  type cmd =
    | Get
    | Set of int_arg
    | Exchange of int_arg
    | Compare_and_set of int_arg * int_arg
    | Fetch_and_add of int_arg
    | Incr
    | Decr [@@deriving qcheck, show { with_path = false }]
  and int_arg = int [@gen Gen.nat]

  type res =
    | RGet of int
    | RSet
    | RExchange of int
    | RFetch_and_add of int
    | RCompare_and_set of bool
    | RIncr
    | RDecr [@@deriving show { with_path = false }]

  let init () = Atomic.make 0

  let run c r = match c with
    | Get                      -> RGet (Atomic.get r)
    | Set i                    -> (Atomic.set r i; RSet)
    | Exchange i               -> RExchange (Atomic.exchange r i)
    | Fetch_and_add i          -> RFetch_and_add (Atomic.fetch_and_add r i)
    | Compare_and_set (seen,v) -> RCompare_and_set (Atomic.compare_and_set r seen v)
    | Incr                     -> (Atomic.incr r; RIncr)
    | Decr                     -> (Atomic.decr r; RDecr)

  let cleanup _ = ()
end

module AT = Lin.Make(AConf)
*)

Util.set_ci_printing ()
;;
QCheck_runner.run_tests_main [
  (*
  IntNAAT.lin_test    ~count:1000 ~name:"non-atomic int array test";
  IntAAT.lin_test    ~count:1000 ~name:"atomic int array test";
  *)
  FloatAAT.lin_test    ~count:1000 ~name:"atomic float array test";
  FloatNAAT.lin_test    ~count:1000 ~name:"non-atomic float array test";
  (*
  IntOptNAAT.lin_test    ~count:1000 ~name:"non-atomic int option array test";
  IntOptAAT.lin_test    ~count:1000 ~name:"atomic int option array test";
  FloatOptNAAT.lin_test    ~count:1000 ~name:"non-atomic float option array test";
  FloatOptAAT.lin_test    ~count:1000 ~name:"atomic float option array test";
  RT.lin_test     ~count:1000 ~name:"ref test";
  CLT.lin_test    ~count:1000 ~name:"CList test";
  AT.lin_test     ~count:1000 ~name:"Atomic test";
  HT.lin_test     ~count:1000 ~name:"Hashtbl test";
  (* Lockfree tests *)
  LFLT.lin_test   ~count:1000 ~name:"lockfree list test";
  LFOLT.lin_test  ~count:1000 ~name:"lockfree ordered list test";
  LFHT.lin_test   ~count:1000 ~name:"lockfree Hash test";
  LFBT.lin_test   ~count:1000 ~name:"lockfree Bag test";
  (* Kcas tests *)
  KT.lin_test     ~count:1000 ~name:"Kcas test";
  KW1T.lin_test   ~count:1000 ~name:"Kcas.W1 test";
  *)
]
