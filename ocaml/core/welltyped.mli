(** Construction of wellformed contexts and welltyped terms. *)


open Fmlib
open Module_types



(** {1 Basics} *)

(** Type of a wellformed context. *)
type context

val empty: context (** An empty context. *)

(** Type of a wellformed context with a term and its type. *)
type judgement


(** Extract the context from the encapsulation. *)
val extract_context: context -> Context.t

(** Extract the judgement from the encapsulation. *)
val extract_judgement: judgement -> Context.t * Term.t * Term.typ






(** {1 Term building} *)

(** A builder for welltyped terms in wellformed contexts. *)
module Builder (Info: ANY):
sig
    type term

    type problem = Info.t * Type_error.t

    (** ['a t] Combinator type building an ['a]. *)
    type _ t

    (** ['a tl] Lazy version of ['a t]. *)
    type 'a tl = unit -> term t

    (** ['a res] The result of a building process. *)
    type 'a res = ('a, problem) result

    (** [make_term c term] Build the term [term] in context [c]. *)
    val make_term: context -> term t -> judgement res


    (** Combinators: Primitive and compound combinators to build terms. *)
    module Construct:
    sig
        val sort:
            Info.t -> Sort.t -> term t

        val variable:
            Info.t -> int -> term t

        val identifier: Info.t -> string -> term t
        (** [identifier info name] Build the term represented by [name]. *)


        val unknown: Info.t -> term t
        (** Unknown term. The compiler is asked to derive. *)


        val application:
            Info.t -> term tl -> term tl -> term t


        (** [lambda name typ exp] Build the lambda term [\ (name: typ) := exp].
         *)
        val lambda:
            Info.t -> string -> term tl -> term tl -> term t


        (** [pi name typ res] Build the product [all (name: typ): res].
         *)
        val pi:
            Info.t -> string -> term tl -> term tl -> term t
    end
end






(** {1 Type checking} *)

(** A type checker. *)
module Check:
sig
    type 'a res = ('a, Type_error.t) result

    (** [check term context] Check [term] in the wellformed [context] and return
        a judgement, i.e.  a welltyped term with its type in the same context or
        return a type error. *)
    val check_term: Term.t -> context -> judgement res
end
