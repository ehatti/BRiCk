(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
Another (incomplete) consistency proof for [PTRS], based on Krebbers' PhD thesis, and
other formal models of C++ using structured pointers.
This is more complex than [SIMPLE_PTRS_IMPL], but will be necessary to justify [VALID_PTR_AXIOMS].

In this model, all valid pointers have an address pinned, but this is not meant
to be guaranteed.
*)

Require Import stdpp.relations.
Require Import stdpp.gmap.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.addr.
Require Import bedrock.prelude.avl.
Require Import bedrock.prelude.bytestring.
Require Import bedrock.prelude.option.
Require Import bedrock.prelude.numbers.

Require Import bedrock.lang.cpp.syntax.
Require Import bedrock.lang.cpp.semantics.sub_module.
Require Import bedrock.lang.cpp.semantics.values.
Require Import bedrock.lang.cpp.model.simple_pointers_utils.
Require Import bedrock.lang.cpp.model.inductive_pointers_utils.
Require Import bedrock.lang.cpp.semantics.ptrs2.

From Equations Require Import Equations.

Axiom irr : ∀ (P : Prop) (p q : P), p = q.

Implicit Types (σ : genv) (z : Z).
#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.

Module PTRS_IMPL <: PTRS_INTF.
  Import canonical_tu address_sums merge_elems.

  Inductive raw_offset_seg : Set :=
  | o_field_ (* type-name: *) (f : field)
  | o_sub_ (ty : type) (z : Z)
  | o_base_ (derived base : globname)
  | o_derived_ (base derived : globname).
  #[local] Instance raw_offset_seg_eq_dec : EqDecision raw_offset_seg.
  Proof. solve_decision. Defined.
  #[global] Declare Instance raw_offset_seg_countable : Countable raw_offset_seg.

  Definition raw_offset := list raw_offset_seg.
  #[local] Instance raw_offset_eq_dec : EqDecision raw_offset := _.
  #[local] Instance raw_offset_countable : Countable raw_offset := _.

  Variant roff_rw_local : raw_offset -> raw_offset -> Prop :=
  | CanonDerBase der base :
    roff_rw_local
      [o_derived_ base der; o_base_ der base]
      []
  | CanonBaseDer der base :
    roff_rw_local
      [o_base_ der base; o_derived_ base der]
      []
  | CanonSubZero ty :
    roff_rw_local
      [o_sub_ ty 0]
      []
  | CanonSubMerge ty n1 n2 :
      roff_rw_local
        [o_sub_ ty n1; o_sub_ ty n2]
        [o_sub_ ty (n1 + n2)].

  Definition roff_rw_global (os1 os2 : raw_offset) :=
    ∃ l r s t,
      os1 = l ++ s ++ r /\
      os2 = l ++ t ++ r /\
      roff_rw_local s t.

  Definition roff_rw := rtc roff_rw_global.

  #[global] Instance: RewriteRelation roff_rw := {}.
  #[global] Instance: subrelation roff_rw_global roff_rw.
  Proof. exact: rtc_once. Qed.
  (* #[global] Instance: Reflexive roff_rw.
  Proof. apply _. Abort.
  #[global] Instance: Transitive roff_rw.
  Proof. apply _. Abort. *)
  Definition roff_canon := nf roff_rw_global.

  #[global] Instance roff_rw_reflexive : Reflexive roff_rw.
  Proof.
    move=> x. done.
  Qed.
  #[global] Instance roff_rw_transitive : Transitive roff_rw.
  Proof.
    move=> x y z. apply rtc_transitive.
  Qed.

  Lemma singleton_offset_canon :
    ∀ o,
      (¬∃ ty, o = o_sub_ ty 0) ->
      roff_canon [o].
  Proof.
    assert (Hn : ∀ A (x y z : A) (l r : list A), [x] ≠ l ++ [y; z] ++ r).
    {
      move=> A x y z l r H.
      destruct l. done.
      inversion H. subst.
      destruct l; done.
    }
    move=> o H.
    rewrite /roff_canon /nf /roff_rw_global /red.
    move=> [_ [l [r [s [t [H1 [_ H2]]]]]]].
    destruct H2.
    { apply: Hn. exact: H1. }
    { apply: Hn. exact: H1. }
    {
      destruct l; simpl in H1;
      inversion H1; subst.
      { apply: H. by exists ty. }
      destruct l; done.
    }
    { apply: Hn. exact: H1. }
  Qed.

  Lemma nil_canon :
    roff_canon [].
  Proof.
    rewrite /roff_canon /roff_rw_global /nf /not /red.
    move=> [o [l [r [s [t [H1 [H2 H3]]]]]]].
    subst.
    assert (l = []).
    { by destruct l. }
    subst.
    assert (s = []).
    { by destruct s. }
    subst.
    clear - H3. remember [].
    by destruct H3.
  Qed.

  Inductive roff_canon_syn : raw_offset -> Prop :=
  | NilCanon :
      roff_canon_syn []
  | SingCanon o :
      ¬(∃ ty, o = o_sub_ ty 0) ->
      roff_canon_syn [o]
  | SubCanon ty i o os :
      roff_canon_syn (o :: os) ->
      ¬(∃ i' ty', o = o_sub_ ty' i') ->
      i ≠ 0 ->
      roff_canon_syn (o_sub_ ty i :: o :: os)
  | FieldCanon f os :
      roff_canon_syn os ->
      roff_canon_syn (o_field_ f :: os)
  | BaseCanon der base o os :
      roff_canon_syn (o :: os) ->
      o ≠ o_derived_ base der ->
      roff_canon_syn (o_base_ der base :: o :: os)
  | DerCanon base der o os :
      roff_canon_syn (o :: os) ->
      o ≠ o_base_ der base ->
      roff_canon_syn (o_derived_ base der :: o :: os).

  Lemma canon_syn_sem_eqv :
    ∀ os,
      roff_canon os <-> roff_canon_syn os.
  Proof.
    rewrite /roff_canon /nf /red.
    move=> os. split; move=> Hc.
    {
      admit.
    }
    {
      induction Hc;
      try (
        remember (o :: os) as eos;
        destruct Hc; subst
      ); try done;
      try inversion Heqeos;
      subst.
      { apply: nil_canon. }
      { by apply: singleton_offset_canon. }
      all:
        move=> [y [l [r [s [t [Ho [Hl Hstep]]]]]]];
        subst; destruct l; simpl in *; destruct Hstep;
        simpl in *; inversion Ho; subst; try done;
        try (
          match goal with
          | H : ¬∃ i ty, o_sub_ _ _ = o_sub_ ty i |- False =>
            apply H
          end;
          try repeat eexists
        );
        try (
          match goal with
          | H : [?o] = ?l ++ ?r |- False =>
            destruct l; simpl in *;
            inversion H; subst;
            destruct l; simpl in *;
            inversion H
          end
        );
        try (
          match goal with
          | H : [?o] = ?l ++ ?r |- False =>
            destruct l; simpl in *;
            inversion H; subst
          end
        );
        try (
          match goal with
          | H : ¬∃ ty, o_sub_ _ 0 = o_sub_ ty 0 |- False =>
              apply H; repeat eexists
          end
        );
        try (
          match goal with
          | H : [] = ?l ++ ?r |- False =>
              destruct l; simpl in *;
              inversion H
          end
        ).
        all: admit.
    }
  Admitted.

  Definition offset := {o : raw_offset | roff_canon o}.
  #[global] Instance offset_eq_dec : EqDecision offset.
  Proof.
    move=> [o1 H1] [o2 H2].
    destruct (decide (o1 = o2)).
    {
      subst. left.
      f_equal.
      apply: irr.
    }
    {
      right.
      rewrite /not => H.
      apply n.
      now apply proj1_sig_eq in H.
    }
  Qed.

  Section norm_def.

    Definition normalize : raw_offset -> raw_offset.
    Admitted.

    Lemma norm_compute :
      

    Lemma norm_sound :
      ∀ os1 os2,
        roff_rw os1 (normalize os2).
    Admitted.

    Lemma norm_complete :
      ∀ os1 os2,
        roff_rw os1 os2 ->
        roff_canon os2 ->
        normalize os1 = os2.
    Admitted.

    Lemma norm_canon :
      ∀ os, roff_canon (normalize os).
    Admitted.

  End norm_def.

  Section norm_lemmas.

    Lemma norm_rw_derive :
      ∀ os1 os2,
        roff_rw os1 os2 ->
        normalize os1 = normalize os2.
    Proof.
      move=> os1 os2 H.
      apply norm_complete.
      { apply norm_sound. }
      { apply norm_canon. }
    Qed.

    Lemma norm_rel :
      ∀ os1 os2,
        normalize os1 = os2 <-> roff_rw os1 os2 /\ roff_canon os2.
    Proof.
      move=> os1 os2.
      split; move=> H.
      {
        subst. split.
        { apply norm_sound. }
        { apply norm_canon. }
      }
      {
        apply norm_complete;
        by destruct H.
      }
    Qed.
  
  End norm_lemmas.

  Section rw_lemmas.

    Lemma roff_rw_cong :
      ∀ ol1 ol2 or1 or2,
        roff_rw ol1 or1 ->
        roff_rw ol2 or2 ->
        roff_rw (ol1 ++ ol2) (or1 ++ or2).
    Proof.
      move=> ol1 ol2 or1 or2 Hrw0 Hrw1.
      induction Hrw0.
      {
        induction Hrw1.
        { done. }
        {
          rewrite -{}IHHrw1.
          apply rtc_once.
          move: H => [l [r [s [t [H1 [H2 H3]]]]]].
          subst. exists (x ++ l), r, s, t.
          split. by rewrite app_assoc.
          split. by rewrite app_assoc.
          done.
        }
      }
      {
        rewrite -{}IHHrw0.
        apply rtc_once.
        move: H => [l [r [s [t [H1 [H2 H3]]]]]].
        subst. exists l, (r ++ ol2), s, t.
        split. by repeat rewrite -app_assoc.
        split. by repeat rewrite -app_assoc.
        done.
      }
    Qed.

    #[global] Instance roff_rw_app_mono :
      Proper (roff_rw ==> roff_rw ==> roff_rw) (++).
    Proof.
      rewrite /Proper /respectful.
      move=> ol1 or1 H1 ol2 or2 H2.
      by apply roff_rw_cong.
    Qed.
    #[global] Instance roff_rw_app_flip_mono :
      Proper (flip roff_rw ==> flip roff_rw ==> flip roff_rw) (++).
    Proof. solve_proper. Qed.

    #[global] Instance roff_rw_cons_mono ro :
      Proper (roff_rw ==> roff_rw) (ro ::.).
    Proof.
      intros x y H.
      by apply roff_rw_cong with (ol1:=[ro]) (or1:=[ro]).
    Qed.

    #[global] Instance roff_rw_cons_flip_mono ro :
      Proper (flip roff_rw ==> flip roff_rw) (ro ::.).
    Proof. solve_proper. Qed.

    #[local] Hint Constructors roff_rw_local : core.

    (* #[global] Instance normalize_mono :
      Proper (roff_rw ==> roff_rw) normalize.
    Proof.
      move=> o1 o2 E.
      move E1: (normalize o1) => o1'.
      move E2: (normalize o2) => o2'.
      move: E1 E2 => /norm_rel [E1 C1] /norm_rel [E2 C2].
      rewrite -E2 -E.
      (* only works for symmetric closure. *)
    Abort. *)

    Lemma norm_invol :
      ∀ os,
        roff_canon os ->
        normalize os = os.
    Proof.
      move=> o H.
      apply norm_complete.
      { constructor. }
      { done. }
    Qed.

    Lemma rw_bwd_r :
      ∀ o1 o2 o2' o3,
        roff_canon o3 ->
        roff_rw o2 o2' ->
        roff_rw (o1 ++ o2) o3 ->
        roff_rw (o1 ++ o2') o3.
    Proof.
      move=> o1 o2 o2' o3 Hc H1 H2.
      induction H1. done.
      move: H => [l [r [s [t [Hx [Hy Hrw]]]]]].
      subst. apply: IHrtc. admit.
    Admitted.

    Lemma norm_absorb_l :
      ∀ o1 o2,
        normalize (o1 ++ normalize o2) = normalize (o1 ++ o2).
    Proof.
      move=> o1 o2.
      rewrite norm_rel.
      split.
      {
        remember (normalize o2) as o2n.
        symmetry in Heqo2n. rewrite norm_rel in Heqo2n.
        remember (normalize (o1 ++ o2)) as ocn.
        symmetry in Heqocn. rewrite norm_rel in Heqocn.
        move: Heqo2n => [Hrw0 Hc0].
        move: Heqocn => [Hrw1 Hc1].
        apply: rw_bwd_r; done.
      }
      { apply: norm_canon. }
    Qed.

    Lemma rw_bwd_l :
      ∀ o1 o1' o2 o3,
        roff_canon o3 ->
        roff_rw o1 o1' ->
        roff_rw (o1 ++ o2) o3 ->
        roff_rw (o1' ++ o2) o3.
    Proof.
      move=> o1 o1' o2 o3 Hc H1 H2.
      induction H1. done.
      apply: IHrtc.
      move: H => [l [r [s [t [Hx [Hy Hrw]]]]]].
      subst. admit.
    Admitted.

    Lemma norm_absorb_r :
      ∀ o1 o2,
        normalize (normalize o1 ++ o2) = normalize (o1 ++ o2).
    Proof.
      move=> o1 o2.
      rewrite norm_rel.
      split.
      {
        remember (normalize o1) as o1n.
        symmetry in Heqo1n. rewrite norm_rel in Heqo1n.
        remember (normalize (o1 ++ o2)) as ocn.
        symmetry in Heqocn. rewrite norm_rel in Heqocn.
        move: Heqo1n => [Hrw0 Hc0].
        move: Heqocn => [Hrw1 Hc1].
        apply: rw_bwd_l; done.
      }
      { apply: norm_canon. }
    Qed.

  End rw_lemmas.

  Inductive root_ptr : Set :=
  | nullptr_
  | global_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | fun_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | alloc_ptr_ (a : alloc_id) (va : vaddr).
  Inductive ptr_ : Set :=
  | invalid_ptr_
  | offset_ptr (p : root_ptr) (o : offset).
  Definition ptr := ptr_.
  #[global] Instance ptr_eq_dec : EqDecision ptr.
  Admitted.
  #[global] Instance ptr_countable : Countable ptr.
  Admitted.

  Program Definition __offset_ptr (p : ptr) (o : offset) : ptr :=
    match p with
    | invalid_ptr_ => invalid_ptr_
    | offset_ptr rp ro => offset_ptr rp (normalize (ro ++ o))
    end.
  Next Obligation.
    (* move=> _ o _ ro. *)
    apply: norm_canon.
    exact: H.
  Qed.

  Program Definition __o_dot (o1 o2 : offset) : offset :=
    normalize (o1 ++ o2).
  Next Obligation.
    (* move=> _ o _ ro. *)
    apply: norm_canon.
    exact: H.
  Qed.

  Include PTRS_SYNTAX_MIXIN.

  Lemma sig_eq {A} {P : A -> Prop} :
  ∀ (x y : A) (p : P x) (q : P y),
    x = y ->
    x ↾ p = y ↾ q.
  Proof.
    move=> x y p q H.
    subst. f_equal.
    apply: irr.
  Qed.

  Program Definition o_id : offset :=
    [].
  Next Obligation.
    by apply: nil_canon.
  Qed.

  #[local] Ltac UNFOLD_dot := rewrite _dot.unlock/DOT_dot/=.

  Lemma id_dot : LeftId (=) o_id o_dot.
  Proof.
    UNFOLD_dot.
    move=> [o H].
    rewrite /o_id /__o_dot.
    simpl. apply: sig_eq.
    by apply norm_invol.
  Qed.

  Lemma dot_id : RightId (=) o_id o_dot.
  Proof.
    UNFOLD_dot.
    move=> [o H].
    rewrite /o_id /__o_dot.
    simpl. apply: sig_eq.
    by rewrite app_nil_r norm_invol.
  Qed.

  Lemma dot_assoc : Assoc (=) o_dot.
  Proof.
    UNFOLD_dot.
    move=> [o1 H1] [o2 H2] [o3 H3].
    rewrite /o_id /__o_dot.
    simpl. apply: sig_eq.
    by rewrite norm_absorb_l norm_absorb_r app_assoc.
  Qed.

  Lemma offset_ptr_id :
    ∀ p : ptr,
      p ,, o_id = p.
  Proof.
    move=> [| r [o H]]; UNFOLD_dot.
    { easy. }
    {
      f_equal. apply: sig_eq.
      by rewrite app_nil_r norm_invol.
    }
  Qed.

  Lemma offset_ptr_dot :
    ∀ (p : ptr) o1 o2,
      p ,, (o1 ,, o2) = p ,, o1 ,, o2.
  Proof.
    move=> [| r o]; UNFOLD_dot.
    { easy. }
    {
      move=> [o1 H1] [o2 H2].
      simpl. f_equal. apply: sig_eq.
      by rewrite norm_absorb_l norm_absorb_r app_assoc.
    }
  Qed.

  Program Definition nullptr : ptr :=
    offset_ptr nullptr_ [].
  Next Obligation.
  Proof.
    by apply: nil_canon.
  Qed.

  Definition invalid_ptr : ptr :=
    invalid_ptr_.

  Program Definition global_ptr (tu : translation_unit) (n : name) : ptr :=
    offset_ptr (global_ptr_ (tu_to_canon tu) n) [].
  Next Obligation.
    (* move=> _ _. *)
    by apply: nil_canon.
  Qed.

  Lemma global_ptr_nonnull :
    ∀ tu o,
      global_ptr tu o ≠ nullptr.
  Proof.
    by done.
  Qed.

  (* Definition eval_raw_offset_seg σ (ro : raw_offset_seg) : option Z :=
    match ro with
    | o_field_ f => o_field_off σ f
    | o_sub_ ty z => o_sub_off σ ty z
    | o_base_ derived base => o_base_off σ derived base
    | o_derived_ base derived => o_derived_off σ base derived
    | o_invalid_ => None
    end.

  Definition mk_offset_seg σ (ro : raw_offset_seg) : offset_seg :=
    match eval_raw_offset_seg σ ro with
    | None => (o_invalid_, 0%Z)
    | Some off => (ro, off)
    end. *)

  Program Definition o_field (f : field) : offset :=
    [o_field_ f].
  Next Obligation.
    (* move=> σ f. *)
    apply: singleton_offset_canon. 2: exact: H.
    clear H. by move=> [ty H].
  Qed.

  Program Definition o_base derived base : offset :=
    [o_base_ derived base].
  Next Obligation.
    (* move=> σ der base. *)
    apply: singleton_offset_canon. 2: exact: H.
    clear H. by move=> [ty H].
  Qed.

  Program Definition o_derived base derived : offset :=
    [o_derived_ base derived].
  Next Obligation.
    (* move=> σ base der. *)
    apply: singleton_offset_canon. 2: exact: H.
    clear H. by move=> [ty H].
  Qed.

  Program Definition o_sub ty z : offset :=
    if decide (z = 0)%Z then
      o_id
    else
      [o_sub_ ty z].
  Next Obligation.
    (* move=> σ ty z znz. *)
    apply: singleton_offset_canon. 2: exact: H.
    clear - n. move=> [ty' H]. congruence.
  Qed.

  #[global] Notation "p ., o" := (_dot p (o_field _ o))
    (at level 11, left associativity, only parsing) : stdpp_scope.
    #[global] Notation "p .[ t ! n ]" := (_dot p (o_sub _ t n))
      (at level 11, left associativity, format "p  .[  t  '!'  n  ]") : stdpp_scope.
    #[global] Notation ".[ t ! n ]" := (o_sub _ t n) (at level 11, no associativity, format ".[  t  !  n  ]") : stdpp_scope.

  Lemma o_sub_0 :
    ∀ ty, o_sub ty 0 = o_id.
  Proof.
    move=> ty.
    rewrite /o_sub.
    by case_match.
  Qed.

  Lemma o_base_derived :
    ∀ (p : ptr) base derived,
      p ,, o_base derived base ,, o_derived base derived = p.
  Proof.
    UNFOLD_dot.
    rewrite /__offset_ptr.
    move=> [| rp [o H]] base der.
    { done. }
    {
      f_equal. simpl. apply: sig_eq.
      rewrite norm_absorb_r -app_assoc norm_rel.
      split.
      {
        simpl. apply: rtc_l. 2: done.
        exists o, [], [o_base_ der base; o_derived_ base der], [].
        split. done.
        split. by repeat rewrite app_nil_r.
        constructor.
      }
      { done. }
    }
  Qed.

  Lemma o_derived_base :
    ∀ (p : ptr) base derived,
      p ,, o_derived base derived ,, o_base derived base = p.
  Proof.
    UNFOLD_dot.
    rewrite /__offset_ptr.
    move=> [| rp [o H]] base der.
    { done. }
    {
      f_equal. simpl. apply: sig_eq.
      rewrite norm_absorb_r -app_assoc norm_rel.
      split.
      {
        simpl. apply: rtc_l. 2: done.
        exists o, [], [o_derived_ base der; o_base_ der base], [].
        split. done.
        split. by repeat rewrite app_nil_r.
        constructor.
      }
      { done. }
    }
  Qed.

  Lemma o_dot_sub :
    ∀ i j ty,
      o_sub ty i ,, o_sub ty j = o_sub ty (i + j).
  Proof.
    UNFOLD_dot.
    move=> i j ty.
    rewrite /__o_dot /o_sub.
    repeat case_match;
    subst; try lia;
    rewrite /o_id; simpl in *;
    apply: sig_eq; try done;
    simp normalize;
    repeat case_match; try done.
    { by replace (i + 0) with i by lia. }
  Qed.

  Definition ptr_alloc_id (p : ptr) : option alloc_id :=
    match p with
    | offset_ptr (alloc_ptr_ a _) _ => Some a
    | _ => None
    end.
  
  Definition null_alloc_id : alloc_id.
  Admitted.
  Lemma ptr_alloc_id_nullptr :
    ptr_alloc_id nullptr = Some null_alloc_id.
  Admitted.

  Lemma ptr_alloc_id_offset :
    ∀ p o,
      is_Some (ptr_alloc_id (p ,, o)) ->
      ptr_alloc_id (p ,, o) = ptr_alloc_id p.
  Proof.
    UNFOLD_dot.
    rewrite /ptr_alloc_id.
    move=> [| r o1] o2; simpl.
    { done. }
    { by destruct r. }
  Qed.

  Definition eval_offset_seg (σ : genv) (o : raw_offset_seg) : option Z :=
    match o with
    | o_field_ f => o_field_off σ f
    | o_sub_ ty i => o_sub_off σ ty i
    | o_base_ der base => o_base_off σ der base
    | o_derived_ base der => o_derived_off σ base der
    end.

  Fixpoint eval_offset_aux (σ : genv) (os : list raw_offset_seg) : option Z :=
    match os with
    | [] => Some 0
    | o :: os =>
      eval_offset_seg σ o ≫= λ o,
      eval_offset_aux σ os ≫= λ os,
      Some (o + os)
    end.

  Definition eval_offset (σ : genv) (os : offset) : option Z :=
    eval_offset_aux σ (`os).

  Lemma eval_o_sub :
    ∀ σ ty (i : Z),
      is_Some (size_of σ ty) ->
      eval_offset σ (o_sub ty i) = (fun n => Z.of_N n * i) <$> size_of σ ty.
  Proof.
    rewrite /eval_offset /o_sub.
    move=> σ ty i [n Hsome].
    case_match; subst; simpl.
    {
      rewrite Hsome. simpl.
      by replace (n * 0) with 0 by lia.
    }
    {
      rewrite /o_sub_off Hsome. simpl.
      by replace (i * n + 0) with (n * i) by lia.
    }
  Qed.

  Lemma eval_o_field :
    ∀ σ n cls st,
      glob_def σ cls = Some (Gstruct st) ->
      st.(s_layout) = POD \/ st.(s_layout) = Standard ->
      eval_offset σ (o_field (Field cls n)) = offset_of σ cls n.
  Proof.
  Admitted.

  Lemma eval_offset_resp_norm :
    ∀ σ os,
      roff_canon os ->
      eval_offset_aux σ (normalize os) = eval_offset_aux σ os.
  Proof.
    move=> σ os Hc.
    by rewrite norm_invol.
  Qed.

  Lemma bind_assoc {A} :
    ∀ (m : option A) (k1 k2 : A -> option A),
      (m >>= k1) >>= k2 = m >>= λ x, k1 x >>= k2.
  Proof.
    move=> m k1 k2.
    by destruct m.
  Qed.

  Lemma canon_uncons :
    ∀ o os,
      roff_canon_syn (o :: os) ->
      roff_canon_syn os.
  Proof.
    move=> o os H.
    remember (o :: os).
    destruct H; try done;
    inversion Heql; subst;
    (constructor || done).
  Qed.

  Lemma eval_offset_dot :
    ∀ σ (o1 o2 : offset) s1 s2,
    eval_offset σ o1 = Some s1 ->
    eval_offset σ o2 = Some s2 ->
    eval_offset σ (o1 ,, o2) = Some (s1 + s2).
  Proof.
    UNFOLD_dot. rewrite /eval_offset.
    move=> σ [o1 H1] [o2 H2] s1 s2 H3 H4. simpl in *.
    remember (normalize (o1 ++ o2)). symmetry in Heqr.
    rewrite norm_rel in Heqr. move: Heqr => [Hrw Hc].

  Qed.

  Definition ptr_vaddr (p : ptr) : option vaddr :=
    match p with
    | invalid_ptr_ => None
    | offset_ptr p (exist _ o _) =>
      foldr
        (λ off ova, Some 1)
        (match p with
        | nullptr_ => Some 0%N
        | fun_ptr_ tu o => Some (global_ptr_encode_vaddr o)
        | global_ptr_ tu o => Some (global_ptr_encode_vaddr o)
        | alloc_ptr_ aid va => Some va
        end)
        o
    end.
End PTRS_IMPL.
