Multicore tests
===============

[![Linux 4.14.0+domains](https://github.com/jmid/multicoretests/actions/workflows/linux-414-workflow.yml/badge.svg)](https://github.com/jmid/multicoretests/actions/workflows/linux-414-workflow.yml)

[![Linux
4.12.0+domains](https://github.com/jmid/multicoretests/actions/workflows/linux-412-workflow.yml/badge.svg)](https://github.com/jmid/multicoretests/actions/workflows/linux-412-workflow.yml)

[![MacOSX
4.12.0+domains](https://github.com/jmid/multicoretests/actions/workflows/macosx-412-workflow.yml/badge.svg)](https://github.com/jmid/multicoretests/actions/workflows/macosx-412-workflow.yml)

Experimental property-based tests of (parts of) the forthcoming OCaml multicore compiler.


Testing for concurrency prompted me to extend [qcstm](https://github.com/jmid/qcstm) to run parallel
state-machine tests akin to [Erlang QuickCheck, Haskell Hedgehog,
ScalaCheck, ...](https://github.com/jmid/pbt-frameworks) This is
experimental code where I'm still playing with various implementation
choices and the interface design (it should probably use GADTs
instead). Consider yourself warned.

[src/STM.ml](src/STM.ml) contains a revision of qcstm that has been
extended with parallel tests. `agree_test` comes in two parallel variants
for now:

 - `agree_test_par` which tests in parallel by `spawn`ing two domains
   from `Domain` directly and
 - `agree_test_pardomlib` which tests in parallel by instead using
   `Domainslib.Task`.

Repeating a non-deterministic property can currently be done in two
different ways:
 - a `repeat`-combinator lets you test a property, e.g., 50 times
   rather than just 1. (Pro: a failure is found faster, Con: wasted,
   repetitive testing when there are no failures)
 - the `Non_det`-module uses a handler into `QCheck` to only perform
   repetition during shrinking. (Pro: each test is cheaper so we can
   run more, Con: more tests are required to trigger a race)

A functor `STM.AddGC` inserts calls to `Gc.minor()` at random points
between the executed commands.

I've used two examples with known problems to ensure that concurrency
issues are indeed found as expected (aka. sanity check). For both of
these a counter example is consistently found and shrunk:

 - [src/ref_test.ml](src/ref_test.ml) tests anunprotected global ref.

 - [src/conclist_test.ml](src/conclist_test.ml) tests a	buggy concurrent list.


A Linearization Tester
======================

Writing a model and specifying how the model changes across each
command requires a bit of effort. This prompted me to carve out a
*linearizability checker* from STM.ml. The resulting, experimental
module `Lin` in [src/lin.ml](src/lin.ml) thus tests that the results
observed during a parallel run is explainable by some linearized,
sequential run of the same commands.

The file [src/lin_tests.ml](src/lin_tests.ml) contains experimental
`Lin`-tests of `Atomic`, `Hashtbl`, `Lockfree.List` (ordered and
unordered), `Lockfree.Hash`, `Lockfree.Bag`, `Kcas`, and `Kcas.W1`
(along with "sanity check tests" for `ref` and `CList`).



Current (experimental) PBTs of multicore
========================================

Tests utilizing the parallel STM.ml capability:

 - [src/atomic_test.ml](src/atomic_test.ml) contains sequential and
   parallel tests of the `Atomic` module using STM.ml

 - [src/ws_deque_test.ml](src/ws_deque_test.ml) contains sequential
   and parallel tests of [ws_deque.ml](https://github.com/ocaml-multicore/domainslib/blob/master/lib/ws_deque.ml)
   from [Domainslib](https://github.com/ocaml-multicore/domainslib).


Tests of the underlying spawn/async functionality of Domain and
Domainslib.Task (not using STM.ml which relies on them):

 - [src/task_one_dep.ml](src/task_one_dep.ml) is a test of `Domainslib.Task`'s `async`/`await`.

 - [src/task_more_deps.ml](src/task_more_deps.ml) is a variant of the
   above allowing each promise to await on multiple others.

 - [src/domain_joingraph.ml](src/domain_joingraph.ml) is a test of `Domain`'s
   `spawn`/`join` based on a random dependency graph

 - [src/domain_spawntree.ml](src/domain_spawntree.ml) is a test of `Domain`'s
   `spawn`/`join` based on a random spawn tree


Issues
======


Specification of `ws_deque`
---------------------------

The initial tests of `ws_deque` just applied the parallelism property `agree_prop_par`.
However that is not sufficient, as only the original domain (thread)
is allowed to call `push`, `pop`, ..., while a `spawn`ed domain
should call only `steal`.

A custom, revised property test in
[src/ws_deque_test.ml](src/ws_deque_test.ml) runs a `cmd` prefix, then
`spawn`s a "stealer domain" with `steal`, ... calls, while the
original domain performs calls across a broder random selection
(`push`, `pop`, ...).

Here is an example output illustrating how `size` may return `-1` when
used in a "stealer domain". The first line in the `Failure` section lists
the original domain's commands and the second lists the stealer
domains commands (`Steal`,...). The second `Messages` section lists a
rough dump of the corresponding return values: `RSteal (Some 73)` is
the result of `Steal`, ... Here it is clear that the spawned domain
successfully steals 73, and then observes both a `-1` and `0` result from
`size` depending on timing. `Size` should therefore not be considered
threadsafe (none of the
[two](https://www.dre.vanderbilt.edu/~schmidt/PDF/work-stealing-dequeue.pdf)
[papers](https://hal.inria.fr/hal-00802885/document) make any such
promises though):

``` ocaml
$ dune exec src/ws_deque_test.exe
random seed: 55610855
generated error  fail  pass / total     time test name
[✗]   318     0     1   317 / 10000     2.4s parallel ws_deque test (w/repeat)

--- Failure --------------------------------------------------------------------

Test parallel ws_deque test (w/repeat) failed (8 shrink steps):

 Seq.prefix:  Parallel procs.:

          []  [(Push 73); Pop; Is_empty; Size]

              [Steal; Size; Size]


+++ Messages ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

Messages for test parallel ws_deque test (w/repeat):

Result observations not explainable by linearized model:

  Seq.prefix:  Parallel procs.:

          []  [RPush; (RPop None); (RIs_empty true); (RSize 0)]

              [(RSteal (Some 73)); (RSize -1); (RSize 0)]

================================================================================
failure (1 tests failed, 0 tests errored, ran 1 tests)
```


Segfault in Domainslib
----------------------

Testing [src/task_one_dep.ml](src/task_one_dep.ml) with 2 work pools
found a [segfault in
domainslib](https://github.com/ocaml-multicore/domainslib/issues/58).





Dead-lock in Domainslib
-----------------------

A reported deadlock in domainslib motivated the development of these tests:
 - https://github.com/ocaml-multicore/domainslib/issues/47
 - https://github.com/ocaml-multicore/ocaml-multicore/issues/670

The tests in [src/task_one_dep.ml](src/task_one_dep.ml) and
[src/task_more_deps.ml](src/task_more_deps.ml) are run with a timeout
to prevent deadlocking indefinitely.

[src/task_one_dep.ml](src/task_one_dep.ml) can trigger one such
deadlock.

It exhibits no non-determistic behaviour when repeating the same
tested property from within the QCheck test.
However it fails (due to timeout) on the following test input:

```ocaml
$ dune exec -- src/task_one_dep.exe -v
random seed: 147821373
generated error fail pass / total     time test name
[✗]   25    0    1   24 /  100    36.2s Task.async/await

--- Failure --------------------------------------------------------------------

Test Task.async/await failed (2 shrink steps):

{ num_domains = 3; length = 6;
  dependencies = [|None; (Some 0); None; (Some 1); None; None|] }
================================================================================
failure (1 tests failed, 0 tests errored, ran 1 tests)
```

This corresponds to the program (available in
[issues/task_issue.ml](issues/task_issue.ml))
with 3+1 domains and 6 promises.
It loops infinitely with both bytecode/native:

```ocaml
...
open Domainslib

(* a simple work item, from ocaml/testsuite/tests/misc/takc.ml *)
let rec tak x y z =
  if x > y then tak (tak (x-1) y z) (tak (y-1) z x) (tak (z-1) x y)
           else z

let work () =
  for _ = 1 to 200 do
    assert (7 = tak 18 12 6);
  done

let pool = Task.setup_pool ~num_additional_domains:3 ()

let p0 = Task.async pool work
let p1 = Task.async pool (fun () -> work (); Task.await pool p0)
let p2 = Task.async pool work
let p3 = Task.async pool (fun () -> work (); Task.await pool p1)
let p4 = Task.async pool work
let p5 = Task.async pool work

let () = List.iter (fun p -> Task.await pool p) [p0;p1;p2;p3;p4;p5]
let () = Task.teardown_pool pool
```


Utop segfault
-------------

Utop segfaults when loading [src/domain_spawntree.ml](src/domain_spawntree.ml)
interactively:

``` ocaml
$ utop
──────────────────────────────────────────────┬─────────────────────────────────────────────────────────────────────┬──────────────────────────────────────────────
                                              │ Welcome to utop version 2.8.0 (using OCaml version 4.12.0+domains)! │                                              
                                              └─────────────────────────────────────────────────────────────────────┘                                              
Findlib has been successfully loaded. Additional directives:
  #require "package";;      to load a package
  #list;;                   to list the available packages
  #camlp4o;;                to load camlp4 (standard syntax)
  #camlp4r;;                to load camlp4 (revised syntax)
  #predicates "p,q,...";;   to set these predicates
  Topfind.reset();;         to force that packages will be reloaded
  #thread;;                 to enable threads


Type #utop_help for help about using utop.

utop # #require "ppx_deriving.show";;
utop # #require "qcheck";;
utop # #use "src/domain_spawntree.ml";;
type cmd = Incr | Decr | Spawn of cmd list
val pp_cmd : Format.formatter -> cmd -> unit = <fun>
val show_cmd : cmd -> string = <fun>
val count_spawns : cmd -> int = <fun>
val gen : int -> int -> cmd Gen.t = <fun>
val shrink_cmd : cmd Shrink.t = <fun>
val interp : int -> cmd -> int = <fun>
val dom_interp : int Atomic.t -> cmd -> unit = <fun>
val t : max_depth:int -> max_width:int -> Test.t = <fun>
random seed: 359528592
Segmentation fault (core dumped)
```

This does not happen when running a plain `ocaml` top-level though, so it
seems `utop`-specific.
