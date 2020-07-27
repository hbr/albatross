(** Construction of wellformed contexts and welltyped terms. *)

open Fmlib
open Module_types


type context = Context.t

let empty: context =
    Context.empty


type judgement = Context.t * Term.t * Term.typ

let extract_context (c: context): Context.t =
    c

let extract_judgement (judge: judgement): Context.t * Term.t * Term.typ =
    judge




module Builder (Info: ANY) =
struct
    module Build = Build.Make (Info)

    type term = Build.term_ref

    type problem = Info.t * Type_error.t

    type 'a res = ('a, problem) result

    type 'a t = Build.t -> ('a * Build.t) res

    type 'a tl = unit -> term t

    let make_term (c: context) (term_builder: term t): judgement res =
        Result.(term_builder (Build.make c)
                >>= fun (term_ref, bc) ->
                let t, typ = Build.get_term term_ref bc in
                Ok (c, t, typ))





    module Construct =
    struct
        let sort (info: Info.t) (s: Sort.t): term t =
            Build.Construct.sort info s


        let variable (_: Info.t) (_: int): term t =
            assert false


        let identifier (info: Info.t) (name: string): term t =
            Build.Construct.identifier info name

        let unknown (_: Info.t): term t =
            assert false

        let application (_: Info.t) (_: term tl) (_: term tl): term t =
            assert false

        let lambda
                (_: Info.t) (_: string) (_: term tl) (_: term tl)
            : term t
            =
            assert false

        let pi
                (_: Info.t) (_: string) (_: term tl) (_: term tl)
            : term t
            =
            assert false
    end
end





module Check =
struct

    module Builder = Builder (Unit)

    type 'a res = ('a, Type_error.t) result


    let check_term (term: Term.t) (c: context): judgement res =
        let rec check term _ =
            let open Builder.Construct
            in
            match term with
            | Term.Sort s ->
                sort () s

            | Term.Appl (f, arg, _) ->
                application () (check f) (check arg)

            | Term.Lambda (argtp, exp, info) ->
                lambda
                    ()
                    (Term.Lambda_info.name info)
                    (check argtp)
                    (check exp)

            | _ ->
                assert false
    in
    Result.map_error
        snd
        (Builder.make_term c (check term ()))
end
