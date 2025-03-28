(*
 * Copyright (C) 2020-2024 BlueRock Security, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: Apache-2.0
 *)
Require Import bluerock.lang.cpp.cpp.
Import cQp_compat.
#[local] Set Warnings "-non-recursive". (* disable warning about [llistR] *)

#[local] Open Scope Z_scope.
#[local] Open Scope bs_scope.

(** * Sequential Specs *)

Section with_Sigma.
Context `{Sigma:cpp_logic} {CU: genv}.

(** ** Range

Consider the following stub

[[
class Range {
private:
    unsigned long _begin;
    size_t _size;
    ...
};
]]

of a [Range] class in C++ implementing contiguous address sets as intervals.
To write specs for C++ functions that operate on [Range]s, we:

(1) Implement a Coq model of the [Range] class;

(2) Write a representation predicate that connects Coq [Range]s to the
    representation of C++ Ranges in memory.

*** Coq Model of [Range]

Let's consider the Coq model first. We build it as a Coq [Record] with
two fields, [begin] and [size], corresponding the the fields of the C++
struct. In our model, we represent both values as [Z]; our representation
predicate will impose additional nonnegativity constraints.
*)

Record Range := { begin : Z; size : Z }.

(**
An example [Range], the interval (inclusive 10, 13), is built as:
 *)

Example range_ex : Range := {| begin := 10; size := 3 |}.

(**
To extract the [begin] and [size] of a [Range] like
[range_ex], one can use projections corresponding to the fields:
 *)

(**Compute range_ex.(begin).*)
(**
     = 10
     : Z
*)

(**Compute range_ex.(size).*)
(**
     = 3
     : Z
 *)

(** *** [Range]: Representation Predicate

Now let's write the representation predicate. It will refer to the
[_begin] and [_size] fields of the C++ struct, which are autogenerated
by cpp2v as:
*)

Notation "'::Range::_begin'" := (Nscoped (Nglobal $ Nid "Range") (Nid "_begin"))
                                (in custom cppglobal at level 0).
Notation "'::Range::_size'" := (Nscoped (Nglobal $ Nid "Range") (Nid "_size"))
                               (in custom cppglobal at level 0).

Definition _begin := _field "Range::_begin".
Definition _size := _field "Range::_size".

(** Here's the first version, which follows the style
discussed in the first chapter.
It's a [Definition] in Coq that takes two
parameters, the fractional permission [q] (which could be 1, indicating
write permission), and [r : Range], the Coq model of the range.
*)

Definition RangeR3 (q : Qp) (r : Range) : Rep :=
  _begin |-> ulongR q r.(begin) ** (*rep star*)
  _size  |-> ulongR q r.(size).

(**
[RangeR3] is a function (predicate), which when applied to a start address ("this"),
will assert the memory representation starting at that address.
This function nature can be made explicit using [as_Rep], which gives
us explicit access to the this pointer as a function argument.
*)
Definition RangeR2 (q : Qp) (r : Range) : Rep :=
  as_Rep (fun this =>
            this |-> (_begin |-> ulongR q r.(begin) ** (*rep star*)
                      _size  |-> ulongR q r.(size))
         ).


(** To make thigs even more explicit, we can distribute the
 [this |->] over the [**]: *)
Definition RangeR1 (q : Qp) (r : Range) : Rep :=
  as_Rep (fun this =>
            this |-> (_begin |-> ulongR q r.(begin)) ** (*mpred star*)
            this |-> (_begin  |-> ulongR q r.(size))
         ).

(**
[[
this |-> (_begin |-> ulongR q r.(begin))
]]

means "at the address [this + offset_of(_begin)]", there's an
unsigned integer r.(begin) held with permission [q].

Access to the "this" pointer is usually not necessary and only adds verbosity.
However, at some places, e.g. in doubly linked lists, it is necessary:
for example, the next node of a doubly linked list stores
the "this" pointer in its prev field.
*)

Definition RangeR := RangeR2.


(** ** Binary Search Trees

In this section, we implement the representation predicate for binary search trees
corresponding to the following C++ struct:

[[
template <typename T = int>
struct Tree {
  T _data;
  Tree<T>* _left;
  Tree<T>* _right;
};
]]

*)

Parameter _data : field.
Parameter _left : field.
Parameter _right : field.
Parameter _Tree : type.

(** *** Unsorted Binary Trees

Following our recipe, we first define a Coq model of (unsorted) trees: *)

Inductive tree (A : Type) : Type :=
| leaf
| node (data : A) (left : tree A) (right : tree A).
Arguments leaf {_}.
Arguments node {_} _ _ _.

(** [leaf] is the empty tree. [node d l r] is the tree node containing
data [d], left subtree [l] and right subtree [r]. [tree] is polymorphic;
it contains data [d] of type [A] for any type [A]. Below, we'll instantiate
[tree] to [A := Z] and to other types.
*)

(** For example, here's the tree with root [3], left child [1], and right
child [5]. *)
Definition ex_tree : tree Z :=
  node 3 (node 1 leaf leaf) (node 5 leaf leaf).

(** We can define pure Coq functions on [tree] for use in specs. For example,
[in_tree x t] is the proposition that reads "tree [x] contains key [t]".
It's defined by recursion on [t].

A leaf never contains a key (represented by [False]).

Key [x] is [in_tree] [node y l r] when:

(1) [x = y]; or

(2) [x] is in the left subtree [l]; or

(3) [x] is in the right subtree [r].
*)

Fixpoint in_tree {A:Type} (x : A) (t : tree A) : Prop :=
  match t with
  | leaf => False
  | node y l r => x=y \/ in_tree x l \/ in_tree x r
  end.

(** Now we define the representation predicate [treeR] for [tree]s.
[treeR] is parameterized inside a [Section] by:

(1) [A : Type], the type of data stored in the trees; and

(2) [R : Qp -> A -> Rep], a representation predicate for [A].

We'll use [R] to define how that data stored in the tree is represented
in memory.
*)

Section treeR.
Context {A : Type} (R : Qp -> A -> Rep).

Fixpoint treeR (q : Qp) (t : tree A) : Rep :=
  as_Rep (fun this =>
            match t with
            | leaf => [| this = nullptr |] (*this |-> nullR*)
            | node d l r =>
              Exists (lp : ptr) (rp : ptr),
              lp |-> treeR q l **
              rp |-> treeR q r **
              this |-> (_field _data |-> R q d **
                        _field _left |-> ptrR<_Tree> q lp **
                        _field _right |-> ptrR<_Tree> q rp)
            end
         ).

(** The [treeR] predicate is defined by recursion on the Coq
tree [t]. Leaves are represented by the [nullptr], which we write as:
[[
[| this = nullptr |]
]]

When the tree is a [node d l r], we assert that field [_data] contains
[R q d] (representation of [d] with permission [q]) and that there exist
pointers [lp] and [rp] stored at the [_left] and [_right] fields.

We separately assert that:

(1) At [lp], there's a [treeR q l], memory implementing the left subtree; and

(2) At [rp], there's a [treeR q r], memory implementing the right subtree.

*)

End treeR.

(** *** Sorted Binary Trees

To build sorted trees from unsorted ones, we define a Coq predicate, [sorted t].
A [leaf] is always sorted. A [node d l r] when [l] is sorted, [r] is sorted,
all the values in [l] are less than [d], and all the values in [r] are greater
than [d]. This definition additionally implies that the tree contains no duplicate
keys.
*)

Section sorted.
Context {A} (lt : A -> A -> Prop).

Fixpoint sorted (t : tree A) : Prop :=
  match t with
  | leaf => True
  | node d l r =>
    sorted l /\
    sorted r /\
    (forall x, in_tree x l -> lt x d) /\
    (forall y, in_tree y r -> lt d y)
  end.
End sorted.

(** The representation predicate [ZbstR q t] uses [sorted] to lift
[treeR] to sorted trees of [Z]s. *)
Definition ZbstR (q : Qp) (t : tree Z) : Rep :=
  treeR (fun q z => uintR q z) q t ** [| sorted Z.lt t |].

(** [(fun q z => uintR q z)] instantiates [treeR]'s parameter [R] to the
representation predicate of unsigned integers. *)

(** *** Count

[count] is a Coq function that computes the number of nodes in a [Coq] tree. *)
Fixpoint count (t : tree Z) : Z :=
  match t with
  | leaf => 0
  | node d l r => 1 + count l + count r
  end.

(**Compute count leaf.*)
(**     = 0
        : Z *)
(**Compute count ex_tree.*)
(**     = 3
        : Z *)

(** [count_spec] uses Coq [count] to specify a C++ function that counts the
number of nodes in a BST:

[[
unsigned int Tree::count() const;
]]
 *)
Definition count_spec (this : ptr) :=
  cpp_spec Tint [] $
  \with (q : Qp) (t : tree Z)
  \prepost this |-> treeR (fun q z => uintR q z) q t
  \post[Vint (trim 32 (count t))] emp.

(**
For more details the syntax/notations for writing the specifications of functions,
please refer to #<a href="https://gitlab.com/bedrocksystems/cpp2v/-/blob/master/doc/specs.md">cpp2v/doc/specs.md</a>#.

We [trim] the count in the postcondition since it might overflow.
Alternatively, we could impose a bounds condition in the precondition:

[[
  \pre [| bound W64 Unsigned (count t) |]
]]

[count] doesn't require that [t] be sorted so the prepost uses just
[treeR], not [ZbstR].
*)

(** *** Insert *)

(** Here's the spec for a function that inserts a key into a tree:

[[
bool Tree::insert(int);
]]

On duplicate keys, [insert] does nothing (we treat the tree as a set rather
than a multiset).
 *)
Definition insert_spec (this : ptr) :=
  cpp_spec Tbool [Tint] $
    \with (t : tree Z)
    \arg{x} "x" (Vint x)
    \pre this |-> ZbstR 1 t
    \post Exists t',
        this |-> ZbstR 1 t' **
        [| forall y, in_tree y t' <-> (y=x \/ in_tree y t) |].

(** More intensionally, we could write this spec using a Coq implementation of
[insert]:
*)
Fixpoint insert x (t : tree Z) : tree Z :=
  match t with
  | leaf => node x leaf leaf
  | node y l r =>
    if Z.ltb x y then node y (insert x l) r
    else if Z.ltb y x then node y l (insert x r)
         else t
  end.

Definition insert_spec' (this : ptr) :=
  cpp_spec Tbool [Tint] $
    \with (t : tree Z)
    \arg{x} "x" (Vint x)
    \pre this |-> ZbstR 1 t
    \post this |-> ZbstR 1 (insert x t).

(** ** EXERCISE: Linked Lists

[FILL_IN] in the representation predicate for linked lists, represented in
Coq by the datatype [llist] and in C++ by the struct:

[[
struct List {
  int _data;
  List* next;
};
]]

The empty linked list is represented by [nullptr].

*)

Parameter _List : type.
Parameter _next : field.

Inductive llist : Type :=
| nil : llist
| cons : Z -> llist -> llist.

Axiom FILL_IN : forall {T}, T. (* Used to mark exercises in this file *)

Fixpoint llistR (q : Qp) (l : llist) : Rep := FILL_IN.

(** ** Range Maps

Here's a Coq model and representation predicate for "Range Maps", binary
trees of [Entries] that associate ranges of addresses to payloads.

[[
  template<typename T>
  struct Entry {
    Range _range;
    T _payload;
  };

  template<typename T>
  using EntryTree = Tree<Entry<T>>;
]]

*)

Parameter _Entry : globname.
Parameter _range : field.
Parameter _payload : field.

(** The Coq model of an [Entry] tracks [Range]s and payloads of type [T]. *)
Record Entry {T : Type} :=
  { range : Range;
    payload : T }.
Arguments Entry _ : clear implicits.

(** Here's the corresponding representation predicate: *)
Definition EntryR (q : Qp) (e : Entry Z) : Rep :=
  _field _range |-> RangeR q e.(range) **
  _field _payload |-> intR q e.(payload).

(** One range is less than another if its [begin] value is less-than. *)
Definition Range_lt (r1 r2 : Range) : Prop :=
  r1.(begin) < r2.(begin).

(** [Entries] are less-than when their [Range]s are less-than. *)
Definition Entry_lt {A} (e1 e2 : Entry A) : Prop :=
  Range_lt e1.(range) e2.(range).

(** A [tree] of [Entries] is sorted if the [Entries] are sorted by [Entry_lt]. *)
Definition Entry_sorted {T} (t : tree (Entry T)) :=
  sorted Entry_lt t.

(** The representation predicate of an [Entry] [BST]: *)
Definition Entry_bstR (q : Qp) (t : tree (Entry Z)) : Rep :=
  treeR EntryR q t ** [| Entry_sorted t |].

(** Putting the pieces together, here's the function spec for
[lookup], which maps an address [x] in a [tree]s of [Entries] to the
corresponding [Entry], if any.  *)

Definition in_range (r : Range) (x : Z) :=
  r.(begin) <= x /\ x < r.(begin) + r.(size).

Definition payload_of_address (t : tree (Entry Z)) (x : Z) (p : Z) : Prop :=
  exists e : Entry Z,
   in_tree e t /\ in_range e.(range) x /\ p = e.(payload).

(** [borrow_from all borrow], which is used in [lookup_spec] below, encapsulates
a pattern for "borrowing" the resources [borrow] from a larger world [all].

With [borrow_from] you get access to two disjoint resources:

(1) You have access to [borrow]; and

(2) If you give up [borrow], you get back [all].
 *)
Definition borrow_from (all borrow : mpred) : mpred :=
  borrow ** (borrow -* all).

(**
Using borrow, we can write the specification for [lookup]:
 *)
Definition lookup_spec (this : ptr) :=
  cpp_spec Tbool [Tint; Tptr Tint] $
    \arg{x} "x" (Vint x)
    \arg{out} "out" (Vptr out)
    \with (q : Qp) (t : tree (Entry Z))
    \pre out |-> anyR (Tptr (Tnamed _Entry)) 1
    \prepost this |-> Entry_bstR q t
    \post{r}[Vbool r]
      (** The postcondition is keyed on the Boolean result [r], with [r=true]
      indicating a successful lookup.*)
      if r then
        (Exists e,
          [| in_tree e t |] **
          [| in_range e.(range) x |] **
          Exists p,
            (** A pointer to the looked-up entry is passed in the
            out parameter [out].*)
            out |-> ptrR<Tnamed _Entry> q p **
            (** We also return a "borrow" from the [Entry_bstR q t], the fact
            that at [p] there's an [EntryR q e] with a matching [Range]. *)
            borrow_from (this |-> Entry_bstR q t) (p |-> EntryR q e))
      else
        (** When [r=false], we assert that there was no payload [p] corresponding
        to the looked-up value [x]. *)
        [| ~exists p, payload_of_address t x p |] **
        (** (Note: This spec allows the implementation to change the [out] parameter
        arbitrarily in the [error] case.) *)
        out |-> anyR Tint 1 **
        this |-> Entry_bstR q t.

End with_Sigma.
