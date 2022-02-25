(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.bi Require Export monpred.
From iris.proofmode Require Import proofmode monpred.
Require Import iris.bi.lib.fractional.

Require Import bedrock.prelude.base.

From bedrock.lang.cpp Require Import semantics.values logic.mpred.
From bedrock.lang.bi Require Import prelude only_provable observe laterable.

Import ChargeNotation.
Implicit Types (σ resolve : genv) (p : ptr) (o : offset).

(** representations are predicates over a location, they should be used to
  * assert properties of the heap
  *)
Canonical Structure ptr_bi_index : biIndex :=
  BiIndex ptr _ eq _.

(** The tactic [intros ->%ptr_rel_elim] is much faster than [intros
    ->] when introducing [p1 ⊑ p2] (when the latter works at all). *)
Lemma ptr_rel_elim (p1 p2 : ptr) : p1 ⊑ p2 → p1 = p2.
Proof. done. Qed.

Definition Rep `{Σ : cpp_logic} := monPred ptr_bi_index mpredI.
Canonical Structure RepI `{Σ : cpp_logic} := monPredI ptr_bi_index mpredI.
Canonical Structure RepO `{Σ : cpp_logic} := monPredO ptr_bi_index mpredI.

Bind Scope bi_scope with Rep.

Section defs.
  Context `{Σ : cpp_logic}.

  Definition as_Rep (P : ptr -> mpred) : Rep := MonPred P _.

  (** [_at base R] states that [R base] holds.

      NOTE This is "weakly at"
   *)
  Definition _at_def (base : ptr) (R : Rep) : mpred :=
    R.(monPred_at) base.
  Definition _at_aux : seal (@_at_def). Proof. by eexists. Qed.
  Definition _at := _at_aux.(unseal).
  Definition _at_eq : @_at = _ := _at_aux.(seal_eq).

  Definition _offsetR_def (o : offset) (r : Rep) : Rep :=
    as_Rep (fun base => r.(monPred_at) (_offset_ptr base o)).
  Definition _offsetR_aux : seal (@_offsetR_def). Proof. by eexists. Qed.
  Definition _offsetR := _offsetR_aux.(unseal).
  Definition _offsetR_eq : @_offsetR = _ := _offsetR_aux.(seal_eq).

  (** Values
   * These `Rep` predicates wrap `ptsto` facts
   *)
  (* todo(gmm): make opaque *)
  Definition pureR (P : mpred) : Rep :=
    as_Rep (fun _ => P).
End defs.

#[global] Instance: Params (@_at) 3 := {}.
#[global] Instance: Params (@as_Rep) 2 := {}.
#[global] Instance: Params (@_offsetR) 3 := {}.
#[global] Instance: Params (@pureR) 2 := {}.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (** See also [Rep_equiv_at] and [Rep_entails_at]. *)
  Lemma Rep_ext (P Q : Rep) :
      (forall p : ptr, P p -|- Q p) ->
      P -|- Q.
  Proof. by constructor. Qed.

  #[global] Instance as_Rep_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) as_Rep.
  Proof. intros R1 R2 HR. constructor=>p. apply HR. Qed.
  #[global] Instance as_Rep_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) as_Rep.
  Proof. intros R1 R2 HR. constructor=>p. apply HR. Qed.

  #[global] Instance as_Rep_mono :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) as_Rep.
  Proof. by constructor. Qed.
  #[global] Instance as_Rep_flip_mono :
    Proper (pointwise_relation _ (flip (⊢)) ==> flip (⊢)) as_Rep.
  Proof. by constructor. Qed.

  #[global] Instance as_Rep_persistent P :
    (∀ p, Persistent (P p)) → Persistent (as_Rep P).
  Proof.
    intros HP. constructor=>p. by rewrite monPred_at_persistently -HP.
  Qed.
  #[global] Instance as_Rep_affine P :
    (∀ p, Affine (P p)) → Affine (as_Rep P) := _.
  #[global] Instance as_Rep_timeless P :
    (∀ p, Timeless (P p)) → Timeless (as_Rep P).
  Proof.
    intros HP. constructor=>p.
    by rewrite monPred_at_later monPred_at_except_0 HP.
  Qed.
  #[global] Instance as_Rep_fractional P :
    (∀ p, Fractional (λ q, P q p)) → Fractional (λ q, as_Rep (P q)).
  Proof.
    intros HP q1 q2. constructor=>p. by rewrite monPred_at_sep /= HP.
  Qed.
  #[global] Instance as_Rep_as_fractional P q :
    (∀ p, AsFractional (P q p) (λ q, P q p) q) →
    AsFractional (as_Rep (P q)) (λ q, as_Rep (P q)) q.
  Proof. constructor. done. apply _. Qed.

  #[global] Instance as_Rep_laterable (R : ptr -> mpred) :
    (∀ p, Laterable (R p)) -> Laterable (as_Rep R).
  Proof.
    rewrite/Laterable=>HR. constructor=>p/=.
    iIntros "R". iDestruct (HR with "R") as (R') "[R #close]".
    rewrite monPred_at_exist. iExists (pureR R').
    rewrite monPred_at_sep monPred_at_later/=. iFrame "R".
    rewrite monPred_at_intuitionistically monPred_at_wand.
    iIntros "!>" (p' ->%ptr_rel_elim).
    by rewrite monPred_at_later monPred_at_except_0/=.
  Qed.

  Lemma as_Rep_emp : as_Rep (λ p, emp) -|- emp.
  Proof. constructor => p. by rewrite monPred_at_emp. Qed.
  Lemma as_Rep_sep P Q : as_Rep (λ p, P p ** Q p) -|- as_Rep P ** as_Rep Q.
  Proof. constructor=>p. by rewrite monPred_at_sep. Qed.

  (* NOTE this is not exposed as a hint *)
  Lemma as_Rep_observe P Q (o : forall p, Observe (P p) (Q p)) : Observe (as_Rep P) (as_Rep Q).
  Proof. apply monPred_observe =>p; apply o. Qed.
  Lemma as_Rep_observe_2 P Q R (o : forall p, Observe2 (P p) (Q p) (R p)) :
    Observe2 (as_Rep P) (as_Rep Q) (as_Rep R).
  Proof. apply monPred_observe_2=>p. apply o. Qed.

  #[global] Instance as_Rep_only_provable_observe Q (P : ptr → mpred) :
    (∀ p, Observe [| Q |] (P p)) → Observe [| Q |] (as_Rep P).
  Proof.
    intros. apply monPred_observe=>p. by rewrite monPred_at_only_provable.
  Qed.
  #[global] Instance as_Rep_only_provable_observe_2 Q (P1 P2 : ptr → mpred) :
    (∀ p, Observe2 [| Q |] (P1 p) (P2 p)) →
    Observe2 [| Q |] (as_Rep P1) (as_Rep P2).
  Proof.
    intros. apply monPred_observe_2=>p. by rewrite monPred_at_only_provable.
  Qed.

  Lemma as_Rep_obs f P :
    (∀ p, f p |-- f p ** [| P |]) →
    as_Rep f |-- as_Rep f ** [| P |].
  Proof.
    intros. apply observe_elim, as_Rep_only_provable_observe =>p. exact: observe_intro.
  Qed.

  Lemma as_Rep_and P Q : as_Rep (λ p, P p //\\ Q p) -|- as_Rep P //\\ as_Rep Q.
  Proof. constructor=>p. by rewrite monPred_at_and. Qed.

  Lemma as_Rep_or P Q : as_Rep (λ p, P p \\// Q p) -|- as_Rep P \\// as_Rep Q.
  Proof. constructor=>p. by rewrite monPred_at_or. Qed.

  Lemma as_Rep_wand P Q : as_Rep (λ p, P p -* Q p) -|- as_Rep P -* as_Rep Q.
  Proof.
    constructor=>p /=. split'.
    - rewrite monPred_at_wand. iIntros "H" (p' ->%ptr_rel_elim) "/= P".
      iApply ("H" with "P").
    - apply monPred_wand_force.
  Qed.

  Lemma as_Rep_exist {T} (P : T -> ptr -> mpred) :
    as_Rep (λ p, Exists x, P x p) -|- Exists x, as_Rep (P x).
  Proof. constructor=>p /=. by rewrite monPred_at_exist. Qed.

  Lemma as_Rep_forall {T} (P : T -> ptr -> mpred) :
    as_Rep (λ p, Forall x, P x p) -|- Forall x, as_Rep (P x).
  Proof. constructor=>p /=. by rewrite monPred_at_forall. Qed.

  Lemma as_Rep_pers P : as_Rep (λ p, <pers> P p) -|- <pers> (as_Rep P).
  Proof. constructor=>p /=. by rewrite monPred_at_persistently. Qed.

  Lemma as_Rep_bupd P : as_Rep (λ p, |==> P p) -|- |==> as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_bupd. Qed.

  Lemma as_Rep_fupd P E1 E2 : as_Rep (λ p, |={E1,E2}=> P p) -|- |={E1,E2}=> as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_fupd. Qed.

  Lemma as_Rep_intuitionistically P : as_Rep (λ p, □ P p) -|- □ as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_intuitionistically. Qed.

  Lemma as_Rep_intuitionistically_if b P : as_Rep (λ p, □?b P p) -|- □?b as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_intuitionistically_if. Qed.

  Lemma as_Rep_except_0 P : as_Rep (λ p, bi_except_0 (P p)) -|- bi_except_0 (as_Rep P).
  Proof. constructor=>p /=. by rewrite monPred_at_except_0. Qed.

  Lemma as_Rep_affinely P : as_Rep (λ p, <affine> P p) -|- <affine> (as_Rep P).
  Proof. constructor=>p /=. by rewrite monPred_at_affinely. Qed.

  Lemma as_Rep_affinely_if b P : as_Rep (λ p, <affine>?b P p) -|- <affine>?b (as_Rep P).
  Proof. constructor=>p /=. by rewrite monPred_at_affinely_if. Qed.

  Lemma as_Rep_big_sepL {T} (l : list T) (F : nat -> T -> ptr -> mpred) :
    as_Rep (λ p, [∗list] i ↦ x ∈ l, F i x p) -|- [∗list] i ↦ x ∈ l, as_Rep (F i x).
  Proof. constructor=>p /=. by rewrite monPred_at_big_sepL. Qed.

  Lemma as_Rep_later P : as_Rep (λ p, |> P p) -|- |> as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_later. Qed.

  Lemma as_Rep_internal_eq (P Q : mpred) : as_Rep (λ _, P ≡ Q) -|- P ≡ Q.
  Proof. constructor=>p /=. by rewrite monPred_at_internal_eq. Qed.

  Lemma Rep_wand_force (R1 R2 : Rep) p : (R1 -* R2) p -|- R1 p -* R2 p.
  Proof. split'. apply monPred_wand_force. by iIntros "a" (? <-%ptr_rel_elim). Qed.
  Lemma Rep_impl_force (R1 R2 : Rep) p : (R1 -->> R2) p -|- R1 p -->> R2 p.
  Proof. split'. apply monPred_impl_force. by iIntros "a" (? <-%ptr_rel_elim). Qed.
  Lemma Rep_at_wand_iff (P Q : Rep) p :
    (P ∗-∗ Q) p ⊣⊢ (P p ∗-∗ Q p).
  Proof. by rewrite /bi_wand_iff monPred_at_and !Rep_wand_force. Qed.

  #[global] Instance _offsetR_ne o n : Proper (dist n ==> dist n) (_offsetR o).
  Proof. rewrite _offsetR_eq. solve_proper. Qed.
  #[global] Instance _offsetR_proper o : Proper ((≡) ==> (≡)) (_offsetR o).
  Proof. rewrite _offsetR_eq. solve_proper. Qed.
  #[global] Instance _offsetR_mono o : Proper ((⊢) ==> (⊢)) (_offsetR o).
  Proof. rewrite _offsetR_eq. solve_proper. Qed.
  #[local] Lemma _offsetR_mono_old : Proper (eq ==> (⊢) ==> (⊢)) _offsetR.
  Proof. solve_proper. Qed.
  #[global] Instance _offsetR_flip_mono o : Proper (flip (⊢) ==> flip (⊢)) (_offsetR o).
  Proof. rewrite _offsetR_eq. solve_proper. Qed.

  #[global] Instance _offsetR_persistent o (r : Rep) :
    Persistent r -> Persistent (_offsetR o r).
  Proof. rewrite _offsetR_eq. apply _. Qed.
  #[global] Instance _offsetR_affine o (r : Rep) :
    Affine r -> Affine (_offsetR o r).
  Proof. rewrite _offsetR_eq. apply _. Qed.
  #[global] Instance _offsetR_timeless o (r : Rep) :
    Timeless r → Timeless (_offsetR o r).
  Proof. rewrite _offsetR_eq. apply _. Qed.
  #[global] Instance _offsetR_laterable o (r : Rep) :
    Laterable r → Laterable (_offsetR o r).
  Proof. rewrite _offsetR_eq. apply _. Qed.

  Lemma _offsetR_offsetR (o1 o2 : offset) R :
    _offsetR o1 (_offsetR o2 R) -|- _offsetR (o_dot o1 o2) R.
  Proof.
    rewrite _offsetR_eq/_offsetR_def/=.
    f_equiv. by intro; rewrite offset_ptr_dot.
  Qed.

  Lemma _offsetR_emp o : _offsetR o emp ⊣⊢ emp.
  Proof.
    rewrite _offsetR_eq /_offsetR_def.
    constructor=> p /=. by rewrite !monPred_at_emp.
  Qed.
  Lemma _offsetR_sep o r1 r2 :
    _offsetR o (r1 ** r2) -|- _offsetR o r1 ** _offsetR o r2.
  Proof.
    rewrite _offsetR_eq /_offsetR_def -as_Rep_sep.
    constructor=> p /=. by rewrite monPred_at_sep.
  Qed.
  Lemma _offsetR_pure (o : offset) (P : Prop) :
    _offsetR o (bi_pure P) -|- bi_pure P.
  Proof.
    rewrite _offsetR_eq/_offsetR_def /=.
    by constructor=> p/=; rewrite !monPred_at_pure.
  Qed.

  Lemma _offsetR_only_provable (o : offset) (P : Prop) :
    _offsetR o [| P |] -|- [| P |].
  Proof.
    rewrite _offsetR_eq/_offsetR_def /=.
    by constructor=> p/=; rewrite !monPred_at_only_provable.
  Qed.

  Lemma _offsetR_and (o : offset) P Q :
    _offsetR o (P //\\ Q) -|- _offsetR o P //\\ _offsetR o Q.
  Proof.
    rewrite _offsetR_eq/_offsetR_def /=.
    by constructor=> p/=; rewrite !monPred_at_and.
  Qed.

  Lemma _offsetR_or (o : offset) P Q :
    _offsetR o (P \\// Q) -|- _offsetR o P \\// _offsetR o Q.
  Proof.
    rewrite _offsetR_eq/_offsetR_def /=.
    by constructor=> p/=; rewrite !monPred_at_or.
  Qed.

  Lemma _offsetR_wand o (P Q : Rep) :
      _offsetR o (P -* Q) -|- _offsetR o P -* _offsetR o Q.
  Proof.
    rewrite !_offsetR_eq /_offsetR_def /=.
    constructor=> p/=. by rewrite !Rep_wand_force.
  Qed.

  Lemma _offsetR_exists o {T} (P : T -> Rep) :
      _offsetR o (Exists v : T, P v) -|- Exists v, _offsetR o (P v).
  Proof. by rewrite _offsetR_eq/_offsetR_def /as_Rep/=; constructor =>p; rewrite /= !monPred_at_exist. Qed.

  Lemma _offsetR_forall o T (P : T -> Rep) :
    _offsetR o (Forall x, P x) -|- Forall x, _offsetR o (P x).
  Proof. by rewrite _offsetR_eq/_offsetR_def /as_Rep/=; constructor =>p; rewrite /= !monPred_at_forall. Qed.

  Lemma _offsetR_pers o R : _offsetR o (<pers> R) -|- <pers> _offsetR o R.
  Proof. by rewrite !_offsetR_eq /_offsetR_def /=; constructor=> p/=; rewrite !monPred_at_persistently. Qed.

  Lemma _offsetR_bupd o R : _offsetR o (|==> R) -|- |==> _offsetR o R.
  Proof. by rewrite _offsetR_eq/_offsetR_def /as_Rep; constructor => p /=; rewrite !monPred_at_bupd. Qed.

  Lemma _offsetR_fupd o R E1 E2 : _offsetR o (|={E1,E2}=> R) -|- |={E1,E2}=> _offsetR o R.
  Proof. by rewrite _offsetR_eq/_offsetR_def /as_Rep; constructor => p /=; rewrite !monPred_at_fupd. Qed.

  Lemma _offsetR_intuitionistically o (R : Rep) : _offsetR o (□ R) ⊣⊢ □ (_offsetR o R).
  Proof. by rewrite _offsetR_eq/_offsetR_def; constructor => p /=; rewrite !monPred_at_intuitionistically. Qed.

  Lemma _offsetR_intuitionistically_if o b R : _offsetR o (□?b R) -|- □?b (_offsetR o R).
  Proof. by destruct b => //=; rewrite _offsetR_intuitionistically. Qed.

  Lemma _offsetR_except_0 o R : _offsetR o (bi_except_0 R) -|- bi_except_0 (_offsetR o R).
  Proof. by rewrite _offsetR_eq/_offsetR_def; constructor => p /=; rewrite !monPred_at_except_0. Qed.

  Lemma _offsetR_affinely (o : offset) R : _offsetR o (<affine> R) -|- <affine> _offsetR o R.
  Proof. by rewrite _offsetR_eq/_offsetR_def /as_Rep; constructor => p/=; rewrite !monPred_at_affinely. Qed.

  Lemma _offsetR_affinely_if b (o : offset) R : _offsetR o (<affine>?b R) -|- <affine>?b _offsetR o R.
  Proof. by destruct b => //; rewrite _offsetR_affinely. Qed.


  Lemma _offsetR_big_sepL (o : offset) {T} (Rs : list T) : forall F,
    _offsetR o ([∗list] i ↦ x ∈ Rs , F i x) -|- [∗list] i ↦ x ∈ Rs , _offsetR o (F i x).
  Proof.
    induction Rs; simpl; intros.
    - by rewrite _offsetR_emp.
    - by rewrite _offsetR_sep IHRs.
  Qed.

  Lemma _offsetR_later o R : _offsetR o (|> R) -|- |> _offsetR o R.
  Proof.
    rewrite _offsetR_eq /_offsetR_def.
    constructor=>p/=. by rewrite !monPred_at_later.
  Qed.

  #[global] Instance _offsetR_fractional o (r : Qp → Rep) :
    Fractional r → Fractional (λ q, _offsetR o (r q)).
  Proof. intros ? q1 q2. by rewrite fractional _offsetR_sep. Qed.
  #[global] Instance _offsetR_as_fractional o (r : Qp → Rep) q :
    Fractional r → AsFractional (_offsetR o (r q)) (λ q, _offsetR o (r q)) q.
  Proof. constructor. done. apply _. Qed.

  #[global] Instance _offsetR_observe {o} {Q R : Rep} :
    Observe Q R ->
    Observe (_offsetR o Q) (_offsetR o R).
  Proof. move->. by rewrite /Observe _offsetR_pers. Qed.

  #[global] Instance _offsetR_observe_2 {o} {Q R1 R2 : Rep} :
    Observe2 Q R1 R2 ->
    Observe2 (_offsetR o Q) (_offsetR o R1) (_offsetR o R2).
  Proof. move->. by rewrite /Observe2 _offsetR_wand _offsetR_pers. Qed.

  #[global] Instance _offsetR_observe_only_provable Q o (R : Rep) :
    Observe [| Q |] R → Observe [| Q |] (_offsetR o R).
  Proof. rewrite -{2}_offsetR_only_provable. apply _. Qed.
  #[global] Instance _offsetR_observe_2_only_provable Q o (R1 R2 : Rep) :
    Observe2 [| Q |] R1 R2 → Observe2 [| Q |] (_offsetR o R1) (_offsetR o R2).
  Proof. rewrite -{2}_offsetR_only_provable. apply _. Qed.

  #[global] Instance _offsetR_observe_pure Q o (R : Rep) :
    Observe [! Q !] R → Observe [! Q !] (_offsetR o R).
  Proof. rewrite -{2}_offsetR_pure. apply _. Qed.
  #[global] Instance _offsetR_observe_2_pure Q o (R1 R2 : Rep) :
    Observe2 [! Q !] R1 R2 → Observe2 [! Q !] (_offsetR o R1) (_offsetR o R2).
  Proof. rewrite -{2}_offsetR_pure. apply _. Qed.

  Lemma _offsetR_obs o r P :
    r |-- r ** [| P |] →
    _offsetR o r |-- _offsetR o r ** [| P |].
  Proof.
    intros. apply observe_elim, _offsetR_observe_only_provable. exact: observe_intro.
  Qed.
  (* Pulled in from plogic. *)
  Lemma _offsetR_id (R : Rep) :
    _offsetR o_id R -|- R.
  Proof.
    rewrite _offsetR_eq /_offsetR_def.
    constructor=>/= p.
    by rewrite offset_ptr_id.
  Qed.

  Lemma _offsetR_dot (o1 o2 : offset) (R : Rep) :
    _offsetR o1 (_offsetR o2 R) -|- _offsetR (o_dot o1 o2) R.
  Proof.
    constructor =>p/=.
    by rewrite _offsetR_eq/_offsetR_def/= offset_ptr_dot.
  Qed.

  #[global] Instance _at_ne l {n} : Proper (dist n ==> dist n) (_at l).
  Proof. rewrite _at_eq. solve_proper. Qed.
  #[global] Instance _at_proper {p} : Proper ((≡) ==> (≡)) (_at p).
  Proof. rewrite _at_eq. solve_proper. Qed.
  #[global] Instance _at_mono {p} : Proper ((⊢) ==> (⊢)) (_at p).
  Proof. rewrite _at_eq. solve_proper. Qed.
  #[global] Instance _at_flip_mono {p} : Proper (flip (⊢) ==> flip (⊢)) (_at p).
  Proof. rewrite _at_eq/_at_def=> r1 r2 HR/=. by rewrite HR. Qed.

  #[global] Instance _at_persistent {P base} : Persistent P -> Persistent (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  #[global] Instance _at_affine {P base} : Affine P -> Affine (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  #[global] Instance _at_timeless {P base} : Timeless P -> Timeless (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  #[global] Instance _at_laterable p (P : Rep) : Laterable P → Laterable (_at p P).
  Proof. rewrite _at_eq. apply _. Qed.

  Lemma Rep_equiv_at (P Q : Rep)
    (HPQ : forall p : ptr, _at p P -|- _at p Q) :
    P -|- Q.
  Proof. constructor => p. move: HPQ => /(_ p). by rewrite _at_eq. Qed.

  Lemma Rep_entails_at (P Q : Rep)
    (HPQ : forall p : ptr, _at p P |-- _at p Q) :
    P |-- Q.
  Proof. constructor => p. move: HPQ => /(_ p). by rewrite _at_eq. Qed.
  (* Inverses of [Rep_equiv_at] and [Rep_entails_at] are [Proper] instances [_at_proper] and [_at_mono], applicable via [f_equiv] or [apply]. *)

  Lemma _at_as_Rep (l : ptr) (Q : ptr → mpred) : _at l (as_Rep Q) ⊣⊢ Q l.
  Proof. by rewrite _at_eq/_at_def. Qed.

  (* Prefer [_at_as_Rep] *)
  Lemma _at_loc p R : _at p R -|- R p.
  Proof. by rewrite _at_eq/_at_def. Qed.

  Lemma _at_emp l : _at l emp -|- emp.
  Proof. by rewrite _at_loc monPred_at_emp. Qed.

  Lemma _at_exists l {T} (P : T -> Rep) :
      _at l (Exists v : T, P v) -|- Exists v, _at l (P v).
  Proof. by rewrite _at_loc monPred_at_exist; setoid_rewrite _at_loc. Qed.

  Lemma _at_forall (l : ptr) T (P : T -> Rep) :
    _at l (Forall x, P x) -|- Forall x, _at l (P x).
  Proof. by rewrite _at_loc monPred_at_forall; setoid_rewrite _at_loc. Qed.

  Lemma _at_only_provable l P :
      _at l [| P |] -|- [| P |].
  Proof. by rewrite _at_loc monPred_at_only_provable. Qed.

  Lemma _at_pure (l : ptr) (P : Prop) :
      _at l [! P !] -|- [! P !].
  Proof. by rewrite _at_loc monPred_at_pure. Qed.

  Lemma _at_sep (l : ptr) (P Q : Rep) :
      _at l (P ** Q) -|- _at l P ** _at l Q.
  Proof. by rewrite !_at_loc monPred_at_sep. Qed.

  Lemma _at_and (l : ptr) (P Q : Rep) :
      _at l (P //\\ Q) -|- _at l P //\\ _at l Q.
  Proof. by rewrite !_at_loc monPred_at_and. Qed.

  Lemma _at_or (l : ptr) (P Q : Rep) :
      _at l (P \\// Q) -|- _at l P \\// _at l Q.
  Proof. by rewrite !_at_loc monPred_at_or. Qed.

  Lemma _at_wand (l : ptr) (P Q : Rep) :
      _at l (P -* Q) -|- _at l P -* _at l Q.
  Proof. by rewrite !_at_loc Rep_wand_force. Qed.

  Lemma _at_pers (l : ptr) R : _at l (<pers> R) -|- <pers> _at l R.
  Proof. by rewrite !_at_loc monPred_at_persistently. Qed.

  Lemma _at_bupd (l : ptr) R : _at l (|==> R) -|- |==> _at l R.
  Proof. by rewrite !_at_loc monPred_at_bupd. Qed.

  Lemma _at_fupd (l : ptr) R E1 E2 : _at l (|={E1,E2}=> R) -|- |={E1,E2}=> _at l R.
  Proof. by rewrite !_at_loc monPred_at_fupd. Qed.

  Lemma _at_intuitionistically l (R : Rep) : _at l (□ R) ⊣⊢ □ (_at l R).
  Proof. by rewrite _at_eq/_at_def monPred_at_intuitionistically. Qed.
  Lemma _at_intuitionistically_if p b R : _at p (□?b R) -|- □?b (_at p R).
  Proof. destruct b => //=. by rewrite _at_intuitionistically. Qed.

  Lemma _at_except_0 p R : _at p (bi_except_0 R) -|- bi_except_0 (_at p R).
  Proof. by rewrite _at_eq/_at_def monPred_at_except_0. Qed.

  Lemma _at_affinely (p : ptr) R : _at p (<affine> R) -|- <affine> _at p R.
  Proof. by rewrite _at_eq/_at_def monPred_at_affinely. Qed.

  Lemma _at_affinely_if b (p : ptr) R : _at p (<affine>?b R) -|- <affine>?b _at p R.
  Proof. by destruct b => //; rewrite _at_eq/_at_def monPred_at_affinely. Qed.

  Lemma _at_later p R : _at p (|> R) -|- |> _at p R.
  Proof. by rewrite _at_eq/_at_def monPred_at_later. Qed.

  Lemma _at_offsetR (l : ptr) (o : offset) (r : Rep) :
      _at l (_offsetR o r) -|- _at (_offset_ptr l o) r.
  Proof. by rewrite !_at_loc /flip _offsetR_eq/_offsetR_def /=. Qed.

  Lemma _at_sepSPs l (xs : list Rep) : _at l ([∗] xs) -|- [∗] map (_at l) xs.
  Proof.
    induction xs => /=.
    - by rewrite _at_emp.
    - by rewrite _at_sep IHxs.
  Qed.

  Lemma _at_big_sepL A l : forall (xs : list A) (Φ : nat -> A -> Rep),
      _at l ([∗ list] i↦x∈xs, Φ i x) -|- ([∗ list] i↦x∈xs, _at l (Φ i x)).
  Proof.
    elim => /=.
    - move => ?; by rewrite _at_emp.
    - move => x xs IH ?. by rewrite _at_sep IH.
  Qed.

  #[global] Instance _at_fractional (r : Qp → Rep) (l : ptr) `{!Fractional r} :
    Fractional (λ q, _at l (r q)).
  Proof.
    intros q1 q2; by rewrite fractional _at_sep.
  Qed.
  #[global] Instance _at_as_fractional (r : Qp → Rep) q (l : ptr)
      `{!AsFractional (r q) r q} :
    AsFractional (_at l (r q)) (λ q, _at l (r q)) q.
  Proof. constructor. done. apply _. Qed.

  #[global] Instance _at_observe {p} {Q R : Rep} :
    Observe Q R ->
    Observe (_at p Q) (_at p R).
  Proof. move->. by rewrite /Observe _at_pers. Qed.

  #[global] Instance _at_observe_2 {p} {Q R1 R2 : Rep} :
    Observe2 Q R1 R2 ->
    Observe2 (_at p Q) (_at p R1) (_at p R2).
  Proof. move->. by rewrite /Observe2 _at_wand _at_pers. Qed.

  #[global] Instance _at_observe_only_provable Q p (R : Rep) :
    Observe [| Q |] R → Observe [| Q |] (_at p R).
  Proof. rewrite -_at_only_provable. apply _. Qed.
  #[global] Instance _at_observe_2_only_provable Q p (R1 R2 : Rep) :
    Observe2 [| Q |] R1 R2 → Observe2 [| Q |] (_at p R1) (_at p R2).
  Proof. rewrite -_at_only_provable. apply _. Qed.

  #[global] Instance _at_observe_pure Q l (R : Rep) :
    Observe [! Q !] R → Observe [! Q !] (_at l R).
  Proof. rewrite -_at_pure. apply _. Qed.
  #[global] Instance _at_observe_2_pure Q l (R1 R2 : Rep) :
    Observe2 [! Q !] R1 R2 → Observe2 [! Q !] (_at l R1) (_at l R2).
  Proof. rewrite -_at_pure. apply _. Qed.

  Lemma _at_obs (l : ptr) (r : Rep) P :
    r |-- r ** [| P |] →
    _at l r |-- _at l r ** [| P |].
  Proof. intros. apply observe_elim, _at_observe_only_provable. exact: observe_intro. Qed.

  #[global] Instance pureR_ne : NonExpansive pureR.
  Proof. solve_proper. Qed.
  #[global] Instance pureR_proper : Proper ((≡) ==> (≡)) pureR.
  Proof. solve_proper. Qed.
  #[global] Instance pureR_mono : Proper ((⊢) ==> (⊢)) pureR.
  Proof. by constructor. Qed.
  #[global] Instance pureR_flip_momo : Proper (flip (⊢) ==> flip (⊢)) pureR.
  Proof. by constructor. Qed.

  #[global] Instance pureR_persistent (P : mpred) :
    Persistent P -> Persistent (pureR P).
  Proof. apply _. Qed.
  #[global] Instance pureR_affine (P : mpred) :
    Affine P -> Affine (pureR P).
  Proof. apply _. Qed.
  #[global] Instance pureR_timeless (P : mpred) :
    Timeless P → Timeless (pureR P).
  Proof. apply _. Qed.
  #[global] Instance pureR_fractional (P : Qp → mpred) :
    Fractional P → Fractional (λ q, pureR (P q)).
  Proof. apply _. Qed.
  #[global] Instance pureR_as_fractional P Φ q :
    AsFractional P Φ q →
    AsFractional (pureR P) (λ q, pureR (Φ q)) q.
  Proof. intros [??]. constructor. done. apply _. Qed.

  #[global] Instance pureR_objective P : Objective (pureR P).
  Proof. done. Qed.

  #[global] Instance pureR_laterable P : Laterable P → Laterable (pureR P).
  Proof. intros. exact: as_Rep_laterable. Qed.

  Lemma pureR_persistently P : pureR (<pers> P) -|- <pers> pureR P.
  Proof. constructor=>p /=. by rewrite monPred_at_persistently. Qed.

  Lemma pureR_only_provable P : pureR [| P |] ⊣⊢ [| P |].
  Proof.
    split'.
    - rewrite (objective_objectively (pureR _)).
      rewrite monPred_objectively_unfold embed_forall.
      by rewrite (bi.forall_elim inhabitant) embed_only_provable.
    - constructor=>p. by rewrite monPred_at_only_provable.
  Qed.

  Lemma pureR_emp : pureR emp -|- emp.
  Proof. exact: as_Rep_emp. Qed.
  Lemma pureR_sep (P Q : mpred) : pureR (P ** Q) -|- pureR P ** pureR Q.
  Proof. exact: as_Rep_sep. Qed.

  Lemma pureR_and (P Q : mpred) : pureR (P //\\ Q) -|- pureR P //\\ pureR Q.
  Proof. exact: as_Rep_and. Qed.

  Lemma pureR_or (P Q : mpred) : pureR (P \\// Q) -|- pureR P \\// pureR Q.
  Proof. exact: as_Rep_or. Qed.

  Lemma pureR_wand (P Q : mpred) : pureR (P -* Q) -|- pureR P -* pureR Q.
  Proof. exact: as_Rep_wand. Qed.

  Lemma pureR_exist {T} (P : T -> mpred) :
    pureR (Exists x, P x) -|- Exists x, pureR (P x).
  Proof. exact: as_Rep_exist. Qed.

  Lemma pureR_forall {T} (P : T -> mpred) :
    pureR (Forall x, P x) -|- Forall x, pureR (P x).
  Proof. exact: as_Rep_forall. Qed.

  Lemma pureR_pers (P : mpred) : pureR (<pers> P) -|- <pers> pureR P.
  Proof. exact: as_Rep_pers. Qed.

  Lemma pureR_bupd (P : mpred) : pureR (|==> P) -|- |==> pureR P.
  Proof. exact: as_Rep_bupd. Qed.

  Lemma pureR_fupd (P : mpred) E1 E2 : pureR (|={E1,E2}=> P) -|- |={E1,E2}=> pureR P.
  Proof. exact: as_Rep_fupd. Qed.

  Lemma pureR_intuitionistically (P : mpred) : pureR (□ P) -|- □ pureR P.
  Proof. exact: as_Rep_intuitionistically. Qed.

  Lemma pureR_intuitionistically_if b (P : mpred) : pureR (□?b P) -|- □?b pureR P.
  Proof. exact: as_Rep_intuitionistically_if. Qed.

  Lemma pureR_except_0 (P : mpred) : pureR (bi_except_0 P) -|- bi_except_0 (pureR P).
  Proof. exact: as_Rep_except_0. Qed.

  Lemma pureR_affinely (P : mpred) : pureR (<affine> P) -|- <affine> pureR P.
  Proof. exact: as_Rep_affinely. Qed.

  Lemma pureR_affinely_if b (P : mpred) : pureR (<affine>?b P) -|- <affine>?b pureR P.
  Proof. exact: as_Rep_affinely_if. Qed.

  Lemma pureR_big_sepL {T} (l : list T) F :
    pureR ([∗list] i ↦ x ∈ l , F i x) -|- [∗list] i ↦ x ∈ l , pureR (F i x).
  Proof. exact: as_Rep_big_sepL. Qed.

  Lemma pureR_later (P : mpred) : pureR (|> P) -|- |> pureR P.
  Proof. exact: as_Rep_later. Qed.

  Lemma pureR_internal_eq (P1 P2 : mpred) : pureR (P1 ≡ P2) -|- P1 ≡ P2.
  Proof. exact: as_Rep_internal_eq. Qed.

  #[global] Instance pureR_observe Q (P : mpred) :
    Observe [| Q |] P → Observe [| Q |] (pureR P).
  Proof. apply _. Qed.
  #[global] Instance pureR_observe_2 Q (P1 P2 : mpred) :
    Observe2 [| Q |] P1 P2 → Observe2 [| Q |] (pureR P1) (pureR P2).
  Proof. apply _. Qed.
  #[global] Instance pureR_observe_pure Q (P : mpred) :
    Observe [! Q !] P → Observe [! Q !] (pureR P).
  Proof.
    intros. apply monPred_observe=>p. by rewrite monPred_at_pure.
  Qed.
  #[global] Instance pureR_observe_2_pure Q (P1 P2 : mpred) :
    Observe2 [! Q !] P1 P2 → Observe2 [! Q !] (pureR P1) (pureR P2).
  Proof.
    intros. apply monPred_observe_2=>p. by rewrite monPred_at_pure.
  Qed.

  Lemma pureR_obs P Q :
    P |-- P ** [| Q |] →
    pureR P |-- pureR P ** [| Q |].
  Proof. intros. apply observe_elim, pureR_observe. exact: observe_intro. Qed.

  Lemma pureR_pure P : pureR ⌜P⌝ ⊣⊢ ⌜P⌝.
  Proof.
    split'.
    - rewrite (objective_objectively (pureR _)).
      rewrite monPred_objectively_unfold embed_forall.
      by rewrite (bi.forall_elim inhabitant) embed_pure.
    - constructor=>p. by rewrite monPred_at_pure.
  Qed.
  Definition pureR_True : pureR True ⊣⊢ True := pureR_pure _.
  Definition pureR_False : pureR False ⊣⊢ False := pureR_pure _.

  Lemma _at_pureR x (P : mpred) : _at x (pureR P) -|- P.
  Proof. by rewrite !_at_loc /pureR. Qed.

  Lemma _offsetR_pureR o P : _offsetR o (pureR P) -|- pureR P.
  Proof. by apply Rep_equiv_at => p; rewrite _at_offsetR !_at_pureR. Qed.

  (** As this isn't syntax-directed, we conservatively avoid
      registering it as an instance (which could slow down
      observations). It's handy under [#[local] Existing Instance
      _at_observe_pureR] to project a [pureR Q] conjunct out of
      representation predicates. *)
  Lemma _at_observe_pureR Q (l : ptr) (R : Rep) :
    Observe (pureR Q) R → Observe Q (_at l R).
  Proof.
    rewrite /Observe=>->. rewrite -pureR_persistently _at_pureR. done.
  Qed.

End with_cpp.

#[global] Typeclasses Opaque _at _offsetR pureR as_Rep.
#[global] Opaque _at _offsetR.
