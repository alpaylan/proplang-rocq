From QuickChick Require Import QuickChick.

From PropLang Require Import PropLang.
Set Warnings "-extraction-opaque-accessed,-extraction".

From BSTProplang Require Import CoverageGenerator.

Axiom num_tests : nat.
Extract Constant num_tests => "max_int".

Definition qctest_test_prop_InsertValid := (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_prop_InsertValid))) ++ "}")).
Definition qctest_test_prop_InsertPost := (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_prop_InsertPost))) ++ "}")).
Definition qctest_test_prop_InsertModel := (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_prop_InsertModel))) ++ "}")).
Definition qctest_test_prop_DeleteInsert := (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_prop_DeleteInsert))) ++ "}")).
Definition qctest_test_prop_InsertInsert := (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_prop_InsertInsert))) ++ "}")).
Definition qctest_test_prop_InsertUnion := (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_prop_InsertUnion))) ++ "}")).
Definition qctest_test_prop_UnionDeleteInsert := (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_prop_UnionDeleteInsert))) ++ "}")).

Parameter OCamlString : Type.
Extract Constant OCamlString => "string".

Axiom qctest_map : OCamlString -> unit.
Extract Constant qctest_map => "
fun test_name ->
  let test_map = [
    (""InsertValid"", qctest_test_prop_InsertValid);
    (""InsertPost"", qctest_test_prop_InsertPost);
    (""InsertModel"", qctest_test_prop_InsertModel);
    (""DeleteInsert"", qctest_test_prop_DeleteInsert);
    (""InsertInsert"", qctest_test_prop_InsertInsert);
    (""InsertUnion"", qctest_test_prop_InsertUnion);
    (""UnionDeleteInsert"", qctest_test_prop_UnionDeleteInsert)
  ] in
  let test = List.assoc test_name test_map in
  test ()


let () =
Sys.argv.(1) |> qctest_map
".


Extraction "CoverageGenerator_test_runner.ml" sample1 runLoop qctest_test_prop_InsertValid qctest_test_prop_InsertPost qctest_test_prop_InsertModel qctest_test_prop_DeleteInsert qctest_test_prop_InsertInsert qctest_test_prop_InsertUnion qctest_test_prop_UnionDeleteInsert qctest_test_prop_InsertValid_coverage qctest_test_prop_InsertPost_coverage qctest_test_prop_InsertModel_coverage qctest_test_prop_DeleteInsert_coverage qctest_test_prop_InsertInsert_coverage qctest_test_prop_InsertUnion_coverage qctest_test_prop_UnionDeleteInsert_coverage qctest_map.
