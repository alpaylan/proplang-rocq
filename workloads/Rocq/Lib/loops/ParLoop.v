Require Import String ZArith List.

From QuickChick Require Import QuickChick.
From PropLang Require Import PropLang.

Import ListNotations.
Import QcNotation.
Import MonadNotation.


Local Open Scope string.
Local Open Scope qc_scope.
Local Open Scope nat_scope.
Local Open Scope Z.
Local Open Scope prop_scope.

(* Axiom parLoop : forall (fuel : nat) (cprop : CProp ∅), unit -> Result.
Extract Constant parLoop => "
      (fun fuel cprop tt ->
      Miou.run  ~domains:4  @@ fun () ->
      let prms = List.init 4 (fun _ -> Miou.call (fun _ -> sample1 (runLoop fuel cprop))) in
      match Miou.await_first prms with
      | Ok value -> value
      | Error exn -> raise exn)
". *)

Axiom parLoop : forall (fuel : nat) (cprop : CProp ∅), unit -> Result.
Extract Constant parLoop => "
  (fun fuel cprop tt ->
    let par =
      (fun new_domain f ->
      let mailbox = Eio.Stream.create 1 in
      let fiber _ () = Eio.Stream.add mailbox (f ()) in
      let domain _ () =
        new_domain (fun () -> fiber |> List.init 1 |> Eio.Fiber.any)
      in
      domain |> List.init 4 |> Eio.Fiber.any;
      Eio.Stream.take mailbox) in
    Eio_main.run @@ fun env ->
    let dmgr = Eio.Stdenv.domain_mgr env in
    let res = par (Eio.Domain_manager.run dmgr) (fun _ -> sample1 (runLoop fuel cprop)) in
    res)
    ".
    