From QuickChick Require Import QuickChick.

From PropLang Require Import PropLang.
Set Warnings "-extraction-opaque-accessed,-extraction".

From IFC Require Import TargetedGenerator.

Definition qctest_test_prop_LLNI := (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_prop_LLNI))) ++ "}")).
Definition qctest_test_prop_SSNI := (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_prop_SSNI))) ++ "}")).

Parameter OCamlString : Type.
Extract Constant OCamlString => "string".

Axiom qctest_map : OCamlString -> unit.
Extract Constant qctest_map => "
fun test_name ->
  let test_map = [
    (""LLNI"", qctest_test_prop_LLNI);
    (""SSNI"", qctest_test_prop_SSNI)
  ] in
  let test = List.assoc test_name test_map in
  test ()

let () =
Sys.argv.(1) |> qctest_map
".

Extraction "TargetedGenerator_test_runner.ml" qctest_test_prop_LLNI qctest_test_prop_SSNI qctest_map.
