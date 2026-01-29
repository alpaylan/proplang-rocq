(* UnifiedStrategies_test_runner.v

   Test runner for all 8 unified strategies.

   Usage: ./UnifiedStrategies_test_runner.native <strategy_name>

   Available strategies:
   - RunLoop_Gen
   - RunLoop_GenExec
   - TargetLoop_Gen_Length
   - TargetLoop_Gen_InstrCov
   - TargetLoop_GenExec_Length
   - TargetLoop_GenExec_InstrCov
   - ThinLoop_Gen_InstrCov
   - ThinLoop_GenExec_InstrCov
*)

From QuickChick Require Import QuickChick.

From PropLang Require Import PropLang.
Set Warnings "-extraction-opaque-accessed,-extraction".

From IFC Require Import UnifiedStrategies.

(* Test function wrappers *)
Definition qctest_test_RunLoop_Gen :=
  (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_RunLoop_Gen))) ++ "}")).

Definition qctest_test_RunLoop_GenExec :=
  (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_RunLoop_GenExec))) ++ "}")).

Definition qctest_test_TargetLoop_Gen_Length :=
  (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_TargetLoop_Gen_Length))) ++ "}")).

Definition qctest_test_TargetLoop_Gen_InstrCov :=
  (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_TargetLoop_Gen_InstrCov))) ++ "}")).

Definition qctest_test_TargetLoop_GenExec_Length :=
  (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_TargetLoop_GenExec_Length))) ++ "}")).

Definition qctest_test_TargetLoop_GenExec_InstrCov :=
  (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_TargetLoop_GenExec_InstrCov))) ++ "}")).

Definition qctest_test_ThinLoop_Gen_InstrCov :=
  (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_ThinLoop_Gen_InstrCov))) ++ "}")).

Definition qctest_test_ThinLoop_GenExec_InstrCov :=
  (fun _ : unit => print_extracted_coq_string ("{" ++ show (withTime(fun tt => (invoke test_ThinLoop_GenExec_InstrCov))) ++ "}")).

Parameter OCamlString : Type.
Extract Constant OCamlString => "string".

Axiom qctest_map : OCamlString -> unit.
Extract Constant qctest_map => "
fun test_name ->
  let test_map = [
    (""RunLoop_Gen"", qctest_test_RunLoop_Gen);
    (""RunLoop_GenExec"", qctest_test_RunLoop_GenExec);
    (""TargetLoop_Gen_Length"", qctest_test_TargetLoop_Gen_Length);
    (""TargetLoop_Gen_InstrCov"", qctest_test_TargetLoop_Gen_InstrCov);
    (""TargetLoop_GenExec_Length"", qctest_test_TargetLoop_GenExec_Length);
    (""TargetLoop_GenExec_InstrCov"", qctest_test_TargetLoop_GenExec_InstrCov);
    (""ThinLoop_Gen_InstrCov"", qctest_test_ThinLoop_Gen_InstrCov);
    (""ThinLoop_GenExec_InstrCov"", qctest_test_ThinLoop_GenExec_InstrCov)
  ] in
  let test = List.assoc test_name test_map in
  test ()

let () =
Sys.argv.(1) |> qctest_map
".

Extraction "UnifiedStrategies_test_runner.ml"
  qctest_test_RunLoop_Gen
  qctest_test_RunLoop_GenExec
  qctest_test_TargetLoop_Gen_Length
  qctest_test_TargetLoop_Gen_InstrCov
  qctest_test_TargetLoop_GenExec_Length
  qctest_test_TargetLoop_GenExec_InstrCov
  qctest_test_ThinLoop_Gen_InstrCov
  qctest_test_ThinLoop_GenExec_InstrCov
  qctest_map.

