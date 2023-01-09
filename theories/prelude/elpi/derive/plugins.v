(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From elpi Require Import elpi.
From elpi.apps Require Import derive.

From stdpp Require Export finite.

From bedrock.prelude Require Export prelude.

Require Import bedrock.prelude.elpi.basis.

Elpi Accumulate derive Db bedrock.basis.db.

(****************************************
 stdpp plugins
 ****************************************)
(*For each supported derivation, two predicates:
   - [myderiv TyGR DerivGR] Maps [TyGR] to its generated derivation
   - [myderiv-done TyGR] We're done deriving [myderiv] for [TyGR].*)
Elpi Db derive.stdpp.db lp:{{
  pred eqdec o:gref, o:gref.
  pred eqdec-done o:gref.

  pred inhabited o:gref, o:gref.
  pred inhabited-done o:gref.

  pred countable o:gref, o:gref.
  pred countable-done o:gref.

  pred finite o:gref, o:gref.
  pred finite-done o:gref.
}}.
Elpi Accumulate derive Db derive.stdpp.db.

(****************************************
 bedrock finite type/bitset (finite.v) plugins
 ****************************************)

 (** Configuration classes: *)
 (** finite type *)
Class ToN (T : Type) (to_N : T -> N) : Type := {}.
#[global] Hint Mode ToN + - : typeclass_instances.
(** bitset *)
Class ToBit (T : Type) (to_bit : T -> N) : Type := {}.
#[global] Hint Mode ToBit + - : typeclass_instances.

Elpi Db derive.finbitset.db lp:{{
  pred finite-type-done o:gref.
  pred bitset-done o:gref.
}}.
Elpi Accumulate derive Db derive.finbitset.db.
