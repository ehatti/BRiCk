(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(**
 * The "operational" style definitions about C++.
 *
 * The definitions in this file are based (loosely) on CompCert.
 *)
Require Import Coq.NArith.BinNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.Ascii.

From Cpp Require Import
     Ast.

(** values *)
Parameter val : Type.

Parameter ptr : Type.
Parameter ptr_eq_dec : forall (x y : ptr), { x = y } + { x <> y }.

Parameter nullptr : ptr.
Parameter Vptr : ptr -> val.
Parameter Vint : Z -> val.

Definition Vchar (a : Ascii.ascii) : val :=
  Vint (Z.of_N (N_of_ascii a)).
Definition Vbool (b : bool) : val :=
  Vint (if b then 1 else 0).


Parameter is_true : val -> bool.
Axiom is_true_int : forall i,
    is_true (Vint i) = negb (BinIntDef.Z.eqb i 0).

Axiom Vptr_inj : forall p1 p2, Vptr p1 = Vptr p2 -> p1 = p2.
Axiom Vint_inj : forall a b, Vint a = Vint b -> a = b.

(* this is the stack frame *)
Parameter region : Type.
(* this is the thread information *)
Parameter thread_info : Type.


(** pointer offsets
 *)
Parameter offset_ptr : val -> Z -> val.
(* note(gmm): this is not defined according to the C semantics because creating
 * a pointer that goes out of bounds of the object is undefined behavior in C,
 * e.g. [(p + a) - a <> p] if [p + a] is out of bounds.
 *)
Axiom offset_ptr_combine : forall b o o',
    offset_ptr (offset_ptr b o) o' = offset_ptr b (o + o').
Axiom offset_ptr_0 : forall b,
    offset_ptr b 0 = b.


(** global environments
 *)
Parameter genv : Type.

Parameter has_type : val -> type -> Prop.

Axiom has_type_pointer : forall v ty, has_type v (Tpointer ty) -> exists p, v = Vptr p.

Definition bound (bits : size) (sgn : signed) (v : Z) : Prop :=
  if sgn then
    (-Z.pow 2 (Z.of_N bits - 1) <= v < Z.pow 2 (Z.of_N bits - 1))%Z
  else
    (0 <= v < Z.pow 2 (Z.of_N bits))%Z.

Axiom has_int_type : forall sz (sgn : signed) z,
    bound sz sgn z <-> has_type (Vint z) (Tint sz sgn).

Axiom has_char_type : forall sz (sgn : signed) z,
    bound sz sgn z <-> has_type (Vint z) (Tchar sz sgn).

Axiom has_type_qual : forall t q x,
    has_type x (drop_qualifiers t) ->
    has_type x (Tqualified q t).

Hint Resolve has_type_qual : has_type.




(* address of a global variable *)
Parameter glob_addr : genv -> obj_name -> ptr -> Prop.

(* todo(gmm): this isn't sound due to reference fields *)
Parameter offset_of : forall (resolve : genv) (t : type) (f : ident) (e : Z), Prop.
Parameter parent_offset : forall (resolve : genv) (t : globname) (f : globname) (e : Z), Prop.

Parameter pointer_size : N. (* in bytes *)


(* sizeof() *)
Parameter size_of : forall (resolve : genv) (t : type) (e : N), Prop.
Axiom size_of_unique : forall {c : genv} t sz sz',
    @size_of c t sz ->
    @size_of c t sz' ->
    sz = sz'.

Axiom size_of_int : forall {c : genv} s w,
    @size_of c (Tint w s) (N.div (w + 7) 8).
Axiom size_of_char : forall {c : genv} s w,
    @size_of c (Tchar w s) (N.div (w + 7) 8).
Axiom size_of_bool : forall {c : genv},
    @size_of c Tbool 1.
Axiom size_of_pointer : forall {c : genv} t,
    @size_of c (Tpointer t) pointer_size.
Axiom size_of_qualified : forall {c : genv} t sz q,
    @size_of c t sz ->
    @size_of c (Tqualified q t) sz.
Axiom size_of_array : forall {c : genv} t n sz,
    @size_of c t sz ->
    @size_of c (Tarray t n) (sz * n).

(* alignof() *)
Parameter align_of : forall {resolve : genv} (t : type) (e : N), Prop.

(* truncation (used for unsigned operations) *)
Definition trim (w : N) (v : Z) : Z := v mod (2 ^ Z.of_N w).
