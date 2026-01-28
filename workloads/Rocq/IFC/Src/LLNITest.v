Require Import IFC.Src.LLNI.
Require Import IFC.Src.SSNI.
Require Import IFC.Src.Machine.
Require Import IFC.Src.TestingCommon.

From mathcomp Require Import ssreflect ssrbool eqtype seq.

(* ========================================================================= *)
(* LLNI/SSNI Property Tests                                                   *)
(* ========================================================================= *)

(* --- LLNI Property Tests --- *)

(* With default_table (CORRECT): Expected Some true - no leak *)
Eval compute in (propLLNI default_table test_variation).

(* With buggy_table_bnz (BUGGY): Expected Some false - leak detected *)
(* Compute (propLLNI buggy_table_bnz test_variation).

(* --- SSNI Property Tests --- *)

(* With default_table (CORRECT): Expected Some true - no leak *)
Compute (propSSNI_smart default_table test_variation).

(* With buggy_table_bnz (BUGGY): Expected Some false - leak detected *)
Compute (propSSNI_smart buggy_table_bnz test_variation). *)
