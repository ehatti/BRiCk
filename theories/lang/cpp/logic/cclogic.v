(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import bedrock.lang.prelude.base.

From iris.bi Require Import lib.fractional.
From iris.base_logic.lib Require Import invariants cancelable_invariants.
From iris.proofmode Require Import tactics.

From bedrock.lang.cpp Require Import logic.pred.

(** This file export the mpred version of own, inv and cinv. *)
(* Right now, they simply shadow Iris' own, inv and cinv, because mpred is still
  iProp. In the future, this will change, and mpred can be come abstract, with
  own/inv/cinv should be features of the logic, not specifically tied to iProp.
  *)

(* own *)
Definition own `{Σ : cpp_logic} `{!inG Σ A} : gname → A → mpred := own.own.
(* TODO: I'll leave sealing for later *)
(* Local Definition own_def `{Σ : cpp_logic} `{!inG Σ A}
  : gname → A → mpred := own.own.
Local Definition own_aux : seal (@own_def). Proof. by eexists. Qed.
Definition own := own_aux.(unseal).
Local Definition own_eq : @own = @own_def := own_aux.(seal_eq). *)
Arguments own {_ Σ A _} γ a.
Instance: Params (@own) 5 := {}.

(* inv *)
Definition inv `{Σ : cpp_logic} `{!invG Σ}
  : namespace → mpred → mpred := invariants.inv.
(* Local Definition inv_def `{Σ : cpp_logic} `{!invG Σ}
  : namespace → mpred → mpred := invariants.inv.
Local Definition inv_aux : seal (@inv_def). Proof. by eexists. Qed.
Definition inv := inv_aux.(unseal).
Local Definition inv_eq : @inv = @inv_def := inv_aux.(seal_eq). *)
Arguments inv {_ Σ _} N P.
Instance: Params (@inv) 4 := {}.

(* cinv *)
Definition cinv_own `{Σ : cpp_logic} `{!invG Σ, !cinvG Σ}
  : gname → frac → mpred := cancelable_invariants.cinv_own.
Arguments cinv_own {_ Σ _ _ } γ a.
Instance: Params (@cinv_own) 5 := {}.

Definition cinv `{Σ : cpp_logic} `{!invG Σ, !cinvG Σ}
  : namespace → gname → mpred → mpred := cancelable_invariants.cinv.
(* Local Definition cinv_def `{Σ : cpp_logic} `{!invG Σ, !cinvG Σ}
  : namespace → gname → mpred → mpred := cancelable_invariants.cinv.
Local Definition cinv_aux : seal (@cinv_def). Proof. by eexists. Qed.
Definition cinv := cinv_aux.(unseal).
Local Definition cinv_eq : @cinv = @cinv_def := cinv_aux.(seal_eq). *)
Arguments cinv {_ Σ _ _} N P.
Instance: Params (@cinv) 6 := {}.

(* the names of invariants *)
Definition iname : Set := namespace.

Bind Scope string_scope with iname.

(* TODO: more to be ported *)
Section own_properties.
  Context `{Σ : cpp_logic, !inG Σ A}.
  Implicit Type (a : A).

  Lemma own_alloc a : ✓ a → |-- |==> Exists γ, own γ a.
  Proof. apply own.own_alloc. Qed.

  Lemma own_alloc_frame a P Q :
    ✓ a ->
    (∀ γ, P ** own γ a |-- Q) ->
    P |-- |==> Q.
  Proof.
    iIntros (VL HQ) "HP".
    iMod (own_alloc a) as (γ) "H"; first done.
    iModIntro. iApply HQ. by iFrame.
  Qed.
End own_properties.

(* TODO: more to be ported *)
Section inv_properties.
  Context `{Σ : cpp_logic, !invG Σ}.
  Implicit Types (P Q : mpred) (γ : gname) (N : namespace) (E : coPset).

  Lemma inv_alloc N E P :
    |> P |-- |={E}=> inv N P.
  Proof. by apply invariants.inv_alloc. Qed.

  #[global] Instance inv_contractive N : Contractive (inv N) := _.
  #[global] Instance inv_ne N : NonExpansive (inv N) := _.
  #[global] Instance inv_proper N : Proper (equiv ==> equiv) (inv N) := _.
  #[global] Instance inv_persistent N P : Persistent (inv N P) := _.
  #[global] Instance inv_affine N P : Affine (inv N P) := _.
End inv_properties.

Section cinv_properties.
  Context `{Σ : cpp_logic, !invG Σ, !cinvG Σ}.
  Implicit Types (P Q : mpred) (γ : gname) (N : namespace) (E : coPset).

  #[global] Instance cinv_own_timeless γ p : Timeless (cinv_own γ p) := _.
  #[global] Instance cinv_contractive N γ : Contractive (cinv N γ) := _.
  #[global] Instance cinv_ne N γ : NonExpansive (cinv N γ) := _.
  #[global] Instance cinv_proper N γ : Proper ((≡) ==> (≡)) (cinv N γ) := _.
  #[global] Instance cinv_persistent N γ P : Persistent (cinv N γ P) := _.
  #[global] Instance cinv_affine N γ P : Affine (cinv N γ P) := _.
  #[global] Instance cinv_own_fractional γ : Fractional (cinv_own γ) := _.
  #[global] Instance cinv_own_as_fractional γ q :
    AsFractional (cinv_own γ q) (cinv_own γ) q := _.


  Lemma cinv_alloc E N P :
    |> P |-- |={E}=> Exists γ, cinv N γ P ** cinv_own γ 1.
  Proof. by apply cancelable_invariants.cinv_alloc. Qed.

  Lemma cinv_cancel E N γ P :
    ↑N ⊆ E →
    cinv N γ P |-- cinv_own γ 1 -* |={E}=> |> P.
  Proof. by apply cancelable_invariants.cinv_cancel. Qed.

  Lemma cinv_alloc_cofinite (G: gset gname) E N :
    |-- |={E}=> Exists γ, ⌜ γ ∉ G ⌝ ** cinv_own γ 1%Qp **
                          ∀ P, |> P ={E}=∗ cinv N γ P.
  Proof. by apply cancelable_invariants.cinv_alloc_cofinite. Qed.

  (* Even stronger: stronger constraints on γ can be picked
    Also see cinv_alloc_strong_open, the invariant can be allocated but
    establishing its content can be delayed. It can be added when needed. *)
  Lemma cinv_alloc_strong (I : gname → Prop) E N :
    pred_infinite I →
    |-- |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗ ∀ I, |> I ={E}=∗ cinv N γ I.
  Proof. by apply cancelable_invariants.cinv_alloc_strong. Qed.

  Corollary cinv_alloc_ghost_named_inv E N (I : gname → mpred) :
    (∀ γ , I γ) |--
    |={E}=> Exists γ, cinv N γ (I γ) ** cinv_own γ 1.
  Proof.
    iIntros "I".
    iMod (cinv_alloc_cofinite empty E N) as (γ ?) "[HO HI]".
    iSpecialize ("I" $! γ).
    iMod ("HI" $! (I γ) with "[$I]") as "HI".
    iIntros "!>". eauto with iFrame.
  Qed.

(*
  Lemma cinv_open_stronger E N γ p P :
    ↑N ⊆ E →
    cinv N γ P ⊢ (cinv_own γ p ={E,E∖↑N}=∗
                  ((|>P) ** cinv_own γ p ** (Forall (E' : coPset), ((|>(P ∨ cinv_own γ 1)) ={E',↑N ∪ E'}=∗ True)))).
  Proof.
    iIntros (?) "Hinv Hown".
    unfold cinv. (* iDestruct "Hinv" as (P') "[#HP' Hinv]". *)
    iPoseProof (inv_acc (↑ N) N _ with "Hinv") as "H"; first done.
    rewrite difference_diag_L.
    iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
    rewrite left_id_L -union_difference_L //. iMod "H" as "[[HP | >HP] H]".
    - iModIntro. iFrame. iDestruct ("HP'" with "HP") as "HP". iFrame. iModIntro.
      iIntros (E') "HP".
      iPoseProof (fupd_mask_frame_r _ _ E' with "(H [HP])") as "H"; first set_solver.
      { iDestruct "HP" as "[HP | >Hown]".
        iLeft. by iApply "HP'".
        eauto.
      }
        by rewrite left_id_L.
    - iDestruct (cinv_own_1_l with "HP Hown") as %[].
  Qed.
*)

  Lemma cinv_acc_strong E N γ p P :
    ↑N ⊆ E →
    cinv N γ P |-- (cinv_own γ p ={E,E∖↑N}=∗
                          (|> P ** cinv_own γ p **
                          (Forall (E' : coPset),
                            ((|> P \\// cinv_own γ 1) ={E',↑N ∪ E'}=∗ True)))).
  Proof. apply cinv_acc_strong. Qed.
End cinv_properties.
