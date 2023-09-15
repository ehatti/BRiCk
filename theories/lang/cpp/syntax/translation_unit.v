(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.fin_maps.
From bedrock.prelude Require Import base avl.
From bedrock.lang.cpp.syntax Require Import names expr stmt types decl.
Export decl.

#[local] Set Primitive Projections.

#[local] Notation EqDecision1 T := (∀ (A : Set), EqDecision A -> EqDecision (T A)) (only parsing).
#[local] Notation EqDecision2 T := (∀ (A : Set), EqDecision A -> EqDecision1 (T A)) (only parsing).
#[local] Notation EqDecision3 T := (∀ (A : Set), EqDecision A -> EqDecision2 (T A)) (only parsing).

#[local] Tactic Notation "solve_decision" := intros; solve_decision.

(* Values in Object files. These can be externed. *)
Variant ObjValue' {classname type Expr : Set} : Set :=
| Ovar         (_ : type) (_ : option Expr)
| Ofunction    (_ : Func' type Expr)
| Omethod      (_ : Method' classname type Expr)
| Oconstructor (_ : Ctor' classname type Expr)
| Odestructor  (_ : Dtor' classname type Expr).
#[global] Arguments ObjValue' _ _ _ : clear implicits, assert.
#[global] Arguments Ovar _ _ _ &.
#[global] Arguments Ofunction _ _ _ &.
#[global] Arguments Omethod _ _ _ &.
#[global] Arguments Oconstructor _ _ _ &.
#[global] Arguments Odestructor _ _ _ &.
#[global] Instance: EqDecision3 ObjValue'.
Proof. solve_decision. Defined.
Notation ObjValue := (ObjValue' globname type Expr).

(**
TODO: [Tmember_func], [type_of_value] seem misplaced
*)

(** [type_of_value o] returns the type of the given [ObjValue] *)
Definition type_of_value (o : ObjValue) : type :=
  normalize_type
  match o with
  | Ovar t _ => t
  | Ofunction f => Tfunction (cc:=f.(f_cc)) (ar:=f.(f_arity)) f.(f_return) $ snd <$> f.(f_params)
  | Omethod m =>
    Tmember_func (Tqualified m.(m_this_qual) (Tnamed m.(m_class))) $ Tfunction (cc:=m.(m_cc)) (ar:=m.(m_arity)) m.(m_return) $ snd <$> m.(m_params)
  | Oconstructor c =>
    Tmember_func (Tnamed c.(c_class)) $ Tfunction (cc:=c.(c_cc)) (ar:=c.(c_arity)) Tvoid $ snd <$> c.(c_params)
  | Odestructor d =>
    Tmember_func (Tnamed d.(d_class)) $ Tfunction (cc:=d.(d_cc)) Tvoid nil
  end.

Variant GlobDecl' {classname type Expr : Set} : Set :=
| Gtype     (* this is a type declaration, but not a definition *)
| Gunion    (_ : Union' type Expr) (* union body *)
| Gstruct   (_ : Struct' classname type Expr) (* struct body *)
| Genum     (_ : type) (_ : list ident) (* *)
| Gconstant (_ : type) (init : option Expr) (* used for enumerator constants*)
| Gtypedef  (_ : type).
#[global] Arguments GlobDecl' _ _ _ : clear implicits, assert.
#[global] Arguments Gunion _ _ _ &.
#[global] Arguments Gstruct _ _ _ &.
#[global] Arguments Genum _ _ _ &.
#[global] Arguments Gconstant _ _ _ &.
#[global] Arguments Gtypedef _ _ _ &.
#[global] Instance: EqDecision3 GlobDecl'.
Proof. solve_decision. Defined.
Notation GlobDecl := (GlobDecl' globname type Expr).

Definition symbol_table : Type := IM.t ObjValue.

Definition type_table : Type := IM.t GlobDecl.

#[global] Instance Singleton_symbol_table : SingletonM obj_name ObjValue symbol_table := _.
#[global] Instance Singleton_type_table : SingletonM globname GlobDecl type_table := _.

(**
TODO: The following work on complete types seems misplaced.
*)

Fixpoint ref_to_type (t : type) : option type :=
  match t with
  | Tref t
  | Trv_ref t => Some t
  | Tqualified _ t => ref_to_type t
  | _ => None
  end.

(* Not a reference type *)
Notation not_ref_type t := (ref_to_type t = None).

Section with_type_table.
  Variable te : type_table.
  (*
  To traverse a type definition and compute, say, its list of subobjects,
  we require that the type is _complete_, as in the usual sense.

  This definition is adapted from Krebbers'15, Definition 3.3.5, with needed
  adjustments for C++.

  Unlike Krebbers:
  - our [type_table] are not ordered
  - [complete_named] takes a proof of [complete_decl] to simplify its use for consumers,
    so we'd naively recheck a struct wherever needed; but an actual checker can
    be smarter (it could use a state monad carrying a map of known-complete types).

  The C++ standard defines and constrains "(in)complete type"s at
  https://eel.is/c++draft/basic.types.general#def:object_type,incompletely-defined,
  and constraints it at https://eel.is/c++draft/basic.scope.pdecl#6,
  https://eel.is/c++draft/class.mem#def:data_member,
  https://eel.is/c++draft/basic.def.odr#12,
  https://eel.is/c++draft/basic.def#5.
  *)

  (* Check that [g : GlobDecl] is complete in environment [te]. *)
  Inductive complete_decl : GlobDecl -> Prop :=
  (* We intentionally omit Krebbers' clauses checking the aggregate is not
  empty: empty aggregates are legal in full C/C++ (see
  [cpp2v-tests/test_translation_unit_validity.cpp]). *)
  | complete_Struct {st}
              (_ : forall b li, In (b, li) st.(s_bases) -> complete_type (Tnamed b))
              (_ : forall m, In m st.(s_fields) -> complete_type m.(mem_type))
    : complete_decl (Gstruct st)
  | complete_Union {u}
              (_ : forall m, In m u.(u_fields) -> complete_type m.(mem_type))
    : complete_decl (Gunion u)
  | complete_enum {t consts} (_ : complete_type t)
    : complete_decl (Genum t consts)
  (* No need for typedefs since those are forbidden in `Tnamed`, `Gtype` isn't
  legal, `Gconstant` is illegal and wouldn't make sense. *)

  (* Basic types. This excludes references (as checked by [complete_basic_type_not_ref]). *)
  with complete_basic_type : type -> Prop :=
  | complete_float sz : complete_basic_type (Tfloat_ sz)
  | complete_int sgn sz : complete_basic_type (Tnum sgn sz)
  | complete_bool : complete_basic_type Tbool
  | complete_void : complete_basic_type Tvoid
  | complete_nullptr : complete_basic_type Tnullptr
  (* t can in turn be a pointer type *)
  | complete_ptr {t} : complete_pointee_type t -> complete_basic_type (Tptr t)

  (* [complete_pointee_type t] says that a pointer/reference to [t] is complete.
     This excludes references (as checked by [complete_pointee_type_not_ref])
     since they cannot be nested. *)
  with complete_pointee_type : type -> Prop :=
  | complete_pt_qualified {q t} (_ : complete_pointee_type t)
    : complete_pointee_type (Tqualified q t)
  (*
    Pointers to array are only legal if the array is complete, at least
    in C, since they cannot actually be indexed or created.
    This rejects the invalid C:

    [struct T; int foo(struct T x[][10]);]

    However, C++ compilers appear to accept this code, which we cover
    in [wellscoped_array].
    *)
  | complete_pt_array t n
    (_ : (n <> 0)%N) (* From Krebbers. Probably needed to reject [T[][]]. *)
    (_ : complete_type t) :
    complete_pointee_type (Tarray t n)
  | complete_pt_named {n decl} :
    (* This check could not appear in a Krebbers-style definition.
       And it is not needed to enable computation on complete types.
     *)
    te !! n = Some decl ->
    complete_pointee_type (Tnamed n)
  | complete_pt_enum {n ty branches} :
    (* This check could not appear in a Krebbers-style definition.
       And it is not needed to enable computation on complete types.
     *)
    te !! n = Some (Genum ty branches) ->
    complete_basic_type ty ->
    complete_pointee_type (Tenum n)

  (* Beware:
  [Tfunction] represents a function type; somewhat counterintuitively,
  a pointer to a function type is complete even if the argument/return types
  are not complete but only well-scoped, you're just forbidden from
  actually invoking the pointer; this follows Krebbers'15 3.3.5. *)
  | complete_pt_function {cc ret args}
      (_ : wellscoped_type ret)
      (_ : wellscoped_types args)
    : complete_pointee_type (Tfunction (cc:=cc) ret args)
  | complete_pt_basic t :
    complete_basic_type t ->
    complete_pointee_type t
  (* [complete_type t] says that type [t] is well-formed, that is, complete. *)
  with complete_type : type -> Prop :=
  | complete_qualified {q t} (_ : complete_type t)
    : complete_type (Tqualified q t)
  (* Reference types. This setup forbids references to references. *)
  | complete_ref {t} : complete_pointee_type t -> complete_type (Tref t)
  | complete_rv_ref {t} : complete_pointee_type t -> complete_type (Trv_ref t)
  (*
  A reference to a struct/union named [n] is well-formed if its definition is.
  TODO: instead of checking that [n] points to a well-formed definition
  _at each occurrence_, check it once, when adding it to our
  analogue of a type environment, that is [type_table].
  However, that might require replacing [type_table] by a _sequence_ of
  declarations, instead of an unordered dictionary.
  *)
  | complete_named {n decl} (_ : te !! n = Some decl)
                    (_ : complete_decl decl) :
    complete_type (Tnamed n)
  | complete_array {t n}
    (_ : (n <> 0)%N) (* Needed? from Krebbers*)
    (_ : complete_type t) :
    complete_type (Tarray t n)
  | complete_member_pointer {n t} (_ : not_ref_type t)
      (_ : complete_pointee_type (Tnamed n))
      (_ : complete_pointee_type t)
    : complete_type (Tmember_pointer n t)
  | complete_function {cc ret args} :
    (*
    We could probably omit this constructor, and consider function types as not
    complete; "complete function types" do not exist in the standard, and
    [complete_symbol_table] does not use the concept.
     *)
    complete_pointee_type (Tfunction (cc:=cc) ret args) ->
    complete_type (Tfunction (cc:=cc) ret args)
  | complete_basic t :
    complete_basic_type t ->
    complete_type t
  (** Well-scoped arguments cannot mention undeclared types. Krebbers identifies
  them with valid pointee, but that breaks down in C++ due to references. *)
  with wellscoped_type : type -> Prop :=
  | wellscoped_qualified {q t} (_ : wellscoped_type t)
    : wellscoped_type (Tqualified q t)
  | wellscoped_array t n
    (_ : (n <> 0)%N) : (* From Krebbers. Probably needed to reject [T[][]]. *)
    wellscoped_type t ->
    wellscoped_type (Tarray t n)
  | wellscoped_pointee t :
    complete_pointee_type t ->
    wellscoped_type t
  (* covers references. *)
  | wellscoped_complete {t} :
    complete_type t ->
    wellscoped_type t
  with wellscoped_types : list type -> Prop :=
  | wellscoped_nil : wellscoped_types []
  | wellscoped_cons t ts :
    wellscoped_type t ->
    wellscoped_types ts ->
    wellscoped_types (t :: ts).

  Inductive valid_decl : GlobDecl -> Prop :=
  | valid_typedef t :
    (*
    All typedefs in use have been inlined at their use-site, so we don't enforce
    their validity.

    In addition, we can't enforce their validity because `clang` produces
    builtin typedefs with ill-scoped bodies, such as
    [(Dtypedef "__NSConstantString" (Tnamed "_Z22__NSConstantString_tag")) :: ... ::
    (Dtypedef "__builtin_va_list" (Tarray (Tnamed "_Z13__va_list_tag") 1)) ::]. *)
    (* wellscoped_type t -> *)
    valid_decl (Gtypedef t)
  | valid_type : valid_decl Gtype
  | valid_const t oe :
    (* Potentially redundant. *)
    wellscoped_type t ->
    valid_decl (Gconstant t oe)
  | valid_complete_decl g :
    complete_decl g -> valid_decl g.
End with_type_table.

Scheme complete_decl_mut_ind := Minimality for complete_decl Sort Prop
with complete_basic_type_mut_ind := Minimality for complete_basic_type Sort Prop
with complete_pointee_type_mut_ind := Minimality for complete_pointee_type Sort Prop
with complete_type_mut_ind := Minimality for complete_type Sort Prop
with wellscoped_type_mut_ind := Minimality for wellscoped_type Sort Prop
with wellscoped_types_mut_ind := Minimality for wellscoped_types Sort Prop.

Combined Scheme complete_mut_ind from complete_decl_mut_ind, complete_basic_type_mut_ind,
  complete_pointee_type_mut_ind, complete_type_mut_ind,
  wellscoped_type_mut_ind, wellscoped_types_mut_ind.

Lemma complete_basic_type_not_ref te t : complete_basic_type te t → not_ref_type t.
Proof. by inversion 1. Qed.
Lemma complete_pointee_type_not_ref te t : complete_pointee_type te t → not_ref_type t.
Proof. induction 1; by [eapply complete_basic_type_not_ref | ]. Qed.

Lemma complete_type_not_ref_ref te t1 t2 : complete_type te t1 → ref_to_type t1 = Some t2 → not_ref_type t2.
Proof.
  induction 1 => Hsome; simplify_eq/=; generalize dependent te => te;
    try by [exact: complete_pointee_type_not_ref| tauto].
  move => /complete_basic_type_not_ref; naive_solver.
Qed.

(**
Adapted from Krebbers'15, Definition 3.3.6:
- all member types must be complete
- all function types must be pointer-complete as defined above.
*)
Definition complete_type_table (te : type_table) :=
  map_Forall (fun _key d => valid_decl te d) te.

Definition complete_symbol_table (te : type_table) (syms : symbol_table) :=
  map_Forall (fun _key d => complete_pointee_type te (type_of_value d)) syms.

Definition complete_translation_unit (te : type_table) (syms : symbol_table) :=
  complete_type_table te /\ complete_symbol_table te syms.

(*
#[global] Instance complete_type_table_dec te : Decision (complete_type_table te).
Proof.
apply: map_Forall_dec.
(* unshelve eapply map_Forall_dec; try apply _. *)
*)

(*
TODOs for FM-216:
1. prove [complete_type_table_dec] above with an efficient checker.
2. add [bool_decide (complete_type_table types = true]) to translation_unit;
   that's automatically proof-irrelevant, and proofs are just cheap [eq_refl].
3. add any helper lemmas, say for proving equality of [translation_unit] from
   equality of the relevant componets.

Twist: the "decision procedure" likely requires fuel; find how to adapt the
above plan. We'll likely end up with a boolean checker proven correct.

Question: do we need [complete_symbol_table]? This is not expected.

Goal: enable recursion on proofs of [complete_type_table], e.g. for defining
[anyR] (FM-215).
*)

Variant GlobalInit' {Expr : Set} : Set :=
  (* initialization by an expression *)
| ExprInit (_ : Expr)
  (* zero initialization *)
| ZeroInit
  (* declaration will be initialized from within a function.
     The C++ standard states that these need to be initialized
     in a concurrency-safe way; however, in practice it is common
     to disable this functionality in embedded code using
     [-fno-threadsafe-statics]. The boolean attached to this
     determines whether *the compiler* guarantees there is at most
     a single call to this constructor.

     See https://eel.is/c++draft/stmt.dcl#3
   *)
| FunctionInit (at_most_once : bool).
#[global] Arguments GlobalInit' _ : clear implicits, assert.
#[global] Arguments ExprInit _ &.
#[global] Instance: EqDecision1 GlobalInit'.
Proof. solve_decision. Defined.
Notation GlobalInit := (GlobalInit' Expr).

(** [GlobalInitializer] represents an initializer for a
    global variable.
 *)
Record GlobalInitializer' {type Expr : Set} : Set := Build_GlobalInitializer
  { g_name : obj_name
  ; g_type : type
  ; g_init : GlobalInit' Expr
  }.
#[global] Arguments GlobalInitializer' _ _ : clear implicits, assert.
#[global] Arguments Build_GlobalInitializer {_ _} &.
#[global] Instance: EqDecision2 GlobalInitializer'.
Proof. solve_decision. Defined.
Notation GlobalInitializer := (GlobalInitializer' type Expr).

(** An initialization block is a sequence of variable initializers
    that will be run when the compilation unit is loaded.

    Note that C++ guarantees the order of some initialization, but
    the order of template initialized global types is not specified by the
    standard.

    This means that, to be completely precise, this type needs to be
    something a bit more exotic that permits concurrent initialization.
 *)
Definition InitializerBlock' (type Expr : Set) : Set :=
  list (GlobalInitializer' type Expr).
Notation InitializerBlock := (InitializerBlock' type Expr).
#[global] Instance InitializerBlock_empty {type Expr} : Empty (InitializerBlock' type Expr) :=
  nil.

(**
A [translation_unit] value represents all the statically known information
about a C++ translation unit, that is, a source file.
TOOD: add support for symbols with _internal_ linkage.
TODO: does linking induce a (non-commutative) monoid on object files? Is then
a translation unit a "singleton" value in this monoid? *)
Record translation_unit : Type :=
{ symbols    : symbol_table
; types    : type_table
; initializer : InitializerBlock
; byte_order : endian
}.

(** These [Lookup] instances come with no theory; use instead the unfolding
    lemmas below and the `fin_maps` theory. *)
#[global] Instance global_lookup : Lookup globname GlobDecl translation_unit :=
  fun k m => m.(types) !! k.
#[global] Instance symbol_lookup : Lookup obj_name ObjValue translation_unit :=
  fun k m => m.(symbols) !! k.

Lemma tu_lookup_globals (t : translation_unit) (n : globname) :
  t !! n = t.(types) !! n.
Proof. done. Qed.

Lemma tu_lookup_symbols (t : translation_unit) (n : obj_name) :
  t !! n = t.(symbols) !! n.
Proof. done. Qed.

(** [is_trivially_destructible tu ty] returns [true] if [ty] is trivially destructible.

    This classifies references as trivially destructible.
 *)
Fixpoint is_trivially_destructible (tu : translation_unit) (ty : type) {struct ty} : bool :=
  qual_norm (fun _ t =>
               match t with
               | Tref _ | Trv_ref _
               | Tnum _ _ | Tchar_ _
               | Tvoid | Tbool | Tptr _
               | Tenum _ => true
               | Tnamed nm =>
                   match tu.(types) !! nm with
                   | Some (Gunion u) => u.(u_trivially_destructible)
                   | Some (Gstruct s) => s.(s_trivially_destructible)
                   | _ => false
                   end
               | Tarray ety _ => is_trivially_destructible tu ety
               | _ => false
               end) ty.
