open QCheck
include Util

module type CmdSpec = sig
  type t
  (** The type of the system under test *)

  type cmd
  (** The type of commands *)

  val show_cmd : cmd -> string
  (** [show_cmd c] returns a string representing the command [c]. *)

  val gen_cmd : cmd Gen.t
  (** A command generator. *)

  type res
  (** The command result type *)

  val show_res : res -> string
  (** [show_res r] returns a string representing the result [r]. *)

  val eq_res : res -> res -> bool

  val init : unit -> t
  (** Initialize the system under test. *)

  val cleanup : t -> unit
  (** Utility function to clean up [t] after each test instance,
      e.g., for closing sockets, files, or resetting global parameters *)

  val run : cmd -> t -> res
  (** [run c t] should interpret the command [c] over the system under test [t] (typically side-effecting). *)
end

module Make(Spec : CmdSpec) (*: StmTest *)
  = struct

  (* operate over arrays to avoid needless allocation underway *)
  let interp sut cs =
    let cs_arr = Array.of_list cs in
    let res_arr = Array.map (fun c -> Domain.cpu_relax(); Spec.run c sut) cs_arr in
    List.combine cs (Array.to_list res_arr)

  (* Note: On purpose we use
     - a non-tail-recursive function and
     - an (explicit) allocation in the loop body
     since both trigger statistically significant more thread issues/interleaving *)
  let rec interp_thread sut cs = match cs with
    | [] -> []
    | c::cs ->
        Thread.yield ();
        let res = Spec.run c sut in
        (c,res)::interp_thread sut cs

  let rec gen_cmds fuel =
    Gen.(if fuel = 0
         then return []
         else
  	  Spec.gen_cmd >>= fun c ->
	   gen_cmds (fuel-1) >>= fun cs ->
             return (c::cs))
  (** A fueled command list generator.
      Accepts a state parameter to enable state-dependent [cmd] generation. *)

  let gen_cmds_size size_gen = Gen.sized_size size_gen gen_cmds

  let shrink_triple =
    let open Iter in
      (fun (seq,p1,p2) ->
        (map (fun seq' -> (seq',p1,p2)) (Shrink.list (*~shrink:shrink_cmd*) seq))
        <+>
        (match p1 with [] -> Iter.empty | c1::c1s -> Iter.return (seq@[c1],c1s,p2))
        <+>
        (match p2 with [] -> Iter.empty | c2::c2s -> Iter.return (seq@[c2],p1,c2s))
        <+>
        (map (fun p1' -> (seq,p1',p2)) (Shrink.list (*~shrink:shrink_cmd*) p1))
        <+>
        (map (fun p2' -> (seq,p1,p2')) (Shrink.list (*~shrink:shrink_cmd*) p2)))

  let arb_cmds_par seq_len par_len =
    let seq_pref_gen = gen_cmds_size (Gen.int_bound seq_len) in
    let par_gen = gen_cmds_size (Gen.int_bound par_len) in
    let gen_triple = Gen.(triple seq_pref_gen par_gen par_gen) in
    make ~print:(print_triple_vertical Spec.show_cmd) ~shrink:shrink_triple gen_triple

  let rec check_seq_cons pref cs1 cs2 seq_sut seq_trace = match pref with
    | (c,res)::pref' ->
        if Spec.eq_res res (Spec.run c seq_sut)
        then check_seq_cons pref' cs1 cs2 seq_sut (c::seq_trace)
        else (Spec.cleanup seq_sut; false)
    (* Invariant: call Spec.cleanup immediately after mismatch  *)
    | [] -> match cs1,cs2 with
            | [],[] -> Spec.cleanup seq_sut; true
            | [],(c2,res2)::cs2' ->
                if Spec.eq_res res2 (Spec.run c2 seq_sut)
                then check_seq_cons pref cs1 cs2' seq_sut (c2::seq_trace)
                else (Spec.cleanup seq_sut; false)
            | (c1,res1)::cs1',[] ->
                if Spec.eq_res res1 (Spec.run c1 seq_sut)
                then check_seq_cons pref cs1' cs2 seq_sut (c1::seq_trace)
                else (Spec.cleanup seq_sut; false)
            | (c1,res1)::cs1',(c2,res2)::cs2' ->
                (if Spec.eq_res res1 (Spec.run c1 seq_sut)
                 then check_seq_cons pref cs1' cs2 seq_sut (c1::seq_trace)
                 else (Spec.cleanup seq_sut; false))
                ||
                (* rerun to get seq_sut to same cmd branching point *)
                (let seq_sut' = Spec.init () in
                 let _ = interp seq_sut' (List.rev seq_trace) in
                 if Spec.eq_res res2 (Spec.run c2 seq_sut')
                 then check_seq_cons pref cs1 cs2' seq_sut' (c2::seq_trace)
                 else (Spec.cleanup seq_sut'; false))

  (* Linearizability property based on [Domain] and an Atomic flag *)
  let lin_prop_domain =
    (fun (seq_pref,cmds1,cmds2) ->
      let sut = Spec.init () in
      let pref_obs = interp sut seq_pref in
      let wait = Atomic.make true in
      let dom1 = Domain.spawn (fun () -> while Atomic.get wait do Domain.cpu_relax() done; interp sut cmds1) in
      let dom2 = Domain.spawn (fun () -> Atomic.set wait false; interp sut cmds2) in
      let obs1 = Domain.join dom1 in
      let obs2 = Domain.join dom2 in
      let ()   = Spec.cleanup sut in
      let seq_sut = Spec.init () in
      check_seq_cons pref_obs obs1 obs2 seq_sut []
      || Test.fail_reportf "  Results incompatible with sequential execution\n\n%s"
         @@ print_triple_vertical ~fig_indent:5 ~res_width:35
              (fun (c,r) -> Printf.sprintf "%s : %s" (Spec.show_cmd c) (Spec.show_res r))
              (pref_obs,obs1,obs2))

  (* Linearizability property based on [Thread] *)
  let lin_prop_thread =
    (fun (seq_pref, cmds1, cmds2) ->
      let sut = Spec.init () in
      let obs1, obs2 = ref [], ref [] in
      let pref_obs = interp sut seq_pref in
      let wait = ref true in
      let th1 = Thread.create (fun () -> while !wait do Thread.yield () done; obs1 := interp_thread sut cmds1) () in
      let th2 = Thread.create (fun () -> wait := false; obs2 := interp_thread sut cmds2) () in
      Thread.join th1;
      Thread.join th2;
      Spec.cleanup sut;
      let seq_sut = Spec.init () in
      (* we reuse [check_seq_cons] to linearize and interpret sequentially *)
      check_seq_cons pref_obs !obs1 !obs2 seq_sut []
      || Test.fail_reportf "  Results incompatible with sequential execution\n\n%s"
         @@ print_triple_vertical ~fig_indent:5 ~res_width:35
              (fun (c,r) -> Printf.sprintf "%s : %s" (Spec.show_cmd c) (Spec.show_res r))
              (pref_obs,!obs1,!obs2))

  (* Linearizability test based on [Domain] *)
  let lin_test ~count ~name (lib : [ `Domain | `Thread ]) =
    let seq_len,par_len = 20,15 in
    let arb_cmd_triple = arb_cmds_par seq_len par_len in
    match lib with
    | `Domain ->
        let rep_count = 50 in
        Test.make ~count ~retries:3 ~name:("Linearizable " ^ name ^ " with Domain")
          arb_cmd_triple (repeat rep_count lin_prop_domain)
    | `Thread ->
        let rep_count = 100 in
        Test.make ~count ~retries:10 ~name:("Linearizable " ^ name ^ " with Thread")
          arb_cmd_triple (repeat rep_count lin_prop_thread)
end
