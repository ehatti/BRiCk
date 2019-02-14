Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.

Local Open Scope Z_scope.
Local Open Scope string_scope.

From ChargeCore.Logics Require Import
     ILogic BILogic ILEmbed Later.

Require Import Cpp.Auto.

Require Demo.A_hpp.
Require Import Demo.A_hpp_spec.

Opaque denoteModule.

Set Nested Proofs Allowed.

(* soundness of the specification *)
Theorem A_hpp_sound : forall (resolve : genv),
    denoteModule A_hpp.module |-- A_hpp_spec resolve.
Proof.
  intros.
  unfold A_hpp_spec.
  work.

  verifyF_forget A__bar.
  { (* A::bar(int) *)
    start_proof.
    simplifying.
    work.
    simplifying.
    work.
    done_proof. }

  finish_module.
Qed.
