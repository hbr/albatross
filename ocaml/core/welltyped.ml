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
    type term

    type problem = Info.t * Type_error.t

    type 'a res = ('a, problem) result

    type bc (* nyi: build context *)

    type 'a t = context -> ('a * bc) res

    type 'a tl = unit -> term t

    let make_term (c: context) (term: term t): judgement res =
        Result.(term c >>= fun (_,_) -> assert false)

    module Construct =
    struct
        let sort (_: Info.t) (_: Sort.t): term t =
            assert false


        let variable (_: Info.t) (_: int): term t =
            assert false


        let application (_: Info.t) (_: term tl) (_: term tl): term t =
            assert false

        let lambda
                (_: Info.t) (_: string) (_: term tl option) (_: term tl)
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
                    (Some (check argtp))
                    (check exp)

            | _ ->
                assert false
    in
    Result.map_error
        snd
        (Builder.make_term c (check term ()))
end
