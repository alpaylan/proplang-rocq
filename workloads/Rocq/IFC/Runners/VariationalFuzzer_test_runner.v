From QuickChick Require Import QuickChick.

From PropLang Require Import PropLang.
Set Warnings "-extraction-opaque-accessed,-extraction".

From IFC Require Import VariationalFuzzer.

Definition qctest_test_prop_SSNI := (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_prop_SSNI))) ++ "}")).

Parameter OCamlString : Type.
Extract Constant OCamlString => "string".

Axiom qctest_map : OCamlString -> unit.
Extract Constant qctest_map => "
fun test_name ->
  let test_map = [
    (""SSNI"", qctest_test_prop_SSNI)
  ] in
  let test = List.assoc test_name test_map in
  test ()

let () =
  Printf.printf ""Entering main of qc_exec\n""; flush stdout;
  setup_shm_aux ();
  Sys.argv.(1) |> qctest_map ; flush stdout;
".

Extraction "VariationalFuzzer_test_runner.ml" sample1 runLoop qctest_test_prop_SSNI qctest_map.
