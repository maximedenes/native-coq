(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(**Untyped intermediate terms, after constr_expr and before constr

   Resolution of names, insertion of implicit arguments placeholder,
   and notations are done, but coercions, inference of implicit
   arguments and pattern-matching compilation are not. *)

open Util
open Names
open Sign
open Term
open Libnames
open Nametab

(**  The kind of patterns that occurs in "match ... with ... end"

     locs here refers to the ident's location, not whole pat *)
type cases_pattern =
  | PatVar of loc * name
  | PatCstr of loc * constructor * cases_pattern list * name 
      (** [PatCstr(p,C,l,x)] = "|'C' 'l' as 'x'" *)

val cases_pattern_loc : cases_pattern -> loc

type patvar = identifier

type glob_sort = GProp of Term.contents | GType of Univ.universe option

type binding_kind = Lib.binding_kind = Explicit | Implicit

type quantified_hypothesis = AnonHyp of int | NamedHyp of identifier

type 'a explicit_bindings = (loc * quantified_hypothesis * 'a) list

type 'a bindings =
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_bindings
  | NoBindings

type 'a with_bindings = 'a * 'a bindings

type 'a cast_type =
  | CastConv of cast_kind * 'a
  | CastCoerce (** Cast to a base type (eg, an underlying inductive type) *)

type glob_constr =
  | GRef of (loc * global_reference)
  | GVar of (loc * identifier)
  | GEvar of loc * existential_key * glob_constr list option
  | GPatVar of loc * (bool * patvar) (** Used for patterns only *)
  | GApp of loc * glob_constr * glob_constr list
  | GLambda of loc * name * binding_kind *  glob_constr * glob_constr
  | GProd of loc * name * binding_kind * glob_constr * glob_constr
  | GLetIn of loc * name * glob_constr * glob_constr
  | GCases of loc * case_style * glob_constr option * tomatch_tuples * cases_clauses
      (** [GCases(l,style,r,tur,cc)] = "match 'tur' return 'r' with 'cc'" (in 
	  [MatchStyle]) *)

  | GLetTuple of loc * name list * (name * glob_constr option) *
      glob_constr * glob_constr
  | GIf of loc * glob_constr * (name * glob_constr option) * glob_constr * glob_constr
  | GRec of loc * fix_kind * identifier array * glob_decl list array *
      glob_constr array * glob_constr array
  | GSort of loc * glob_sort
  | GHole of (loc * Evd.hole_kind)
  | GCast of loc * glob_constr * glob_constr cast_type
  | GDynamic of loc * Dyn.t
  | GNativeInt of loc * Uint31.t
  | GNativeArr of loc * rawconstr * rawconstr array

and glob_decl = name * binding_kind * glob_constr option * glob_constr

and fix_recursion_order = GStructRec | GWfRec of glob_constr | GMeasureRec of glob_constr * glob_constr option

and fix_kind =
  | GFix of ((int option * fix_recursion_order) array * int)
  | GCoFix of int

and predicate_pattern =
    name * (loc * inductive * int * name list) option
      (** [(na,id)] = "as 'na' in 'id'" where if [id] is [Some(l,I,k,args)], [k]
	  is the number of parameter of [I]. *)

and tomatch_tuple = (glob_constr * predicate_pattern)

and tomatch_tuples = tomatch_tuple list

and cases_clause = (loc * identifier list * cases_pattern list * glob_constr)
(** [(p,il,cl,t)] = "|'cl' as 'il' => 't'" *)

and cases_clauses = cases_clause list

val cases_predicate_names : tomatch_tuples -> name list

val map_glob_constr : (glob_constr -> glob_constr) -> glob_constr -> glob_constr

(* Ensure traversal from left to right *)
val map_glob_constr_left_to_right :
  (glob_constr -> glob_constr) -> glob_constr -> glob_constr

(*
val map_glob_constr_with_binders_loc : loc ->
  (identifier -> 'a -> identifier * 'a) ->
  ('a -> glob_constr -> glob_constr) -> 'a -> glob_constr -> glob_constr
*)

val fold_glob_constr : ('a -> glob_constr -> 'a) -> 'a -> glob_constr -> 'a
val iter_glob_constr : (glob_constr -> unit) -> glob_constr -> unit
val occur_glob_constr : identifier -> glob_constr -> bool
val free_glob_vars : glob_constr -> identifier list
val loc_of_glob_constr : glob_constr -> loc

(** Conversion from glob_constr to cases pattern, if possible
    
    Take the current alias as parameter, 
    @raise Not_found if translation is impossible *)
val cases_pattern_of_glob_constr : name -> glob_constr -> cases_pattern

val glob_constr_of_closed_cases_pattern : cases_pattern -> name * glob_constr

(** {6 Reduction expressions} *)

type 'a glob_red_flag = {
  rBeta : bool;
  rIota : bool;
  rZeta : bool;
  rDelta : bool; (** true = delta all but rConst; false = delta only on rConst*)
  rConst : 'a list
}

val all_flags : 'a glob_red_flag

type 'a or_var = ArgArg of 'a | ArgVar of identifier located

type occurrences_expr = bool * int or_var list

val all_occurrences_expr_but : int or_var list -> occurrences_expr
val no_occurrences_expr_but : int or_var list -> occurrences_expr
val all_occurrences_expr : occurrences_expr
val no_occurrences_expr : occurrences_expr

type 'a with_occurrences = occurrences_expr * 'a

type ('a,'b,'c) red_expr_gen =
  | Red of bool
  | Hnf
  | Simpl of 'c with_occurrences option
  | Cbv of 'b glob_red_flag
  | Lazy of 'b glob_red_flag
  | Unfold of 'b with_occurrences list
  | Fold of 'a list
  | Pattern of 'a with_occurrences list
  | ExtraRedExpr of string
  | CbvVm
  | CbvNbe

type ('a,'b,'c) may_eval =
  | ConstrTerm of 'a
  | ConstrEval of ('a,'b,'c) red_expr_gen * 'a
  | ConstrContext of (loc * identifier) * 'a
  | ConstrTypeOf of 'a
