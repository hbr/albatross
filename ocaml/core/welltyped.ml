(** Construction of wellformed contexts and welltyped terms. *)

open Fmlib
open Module_types


type context = Context.t

type judgement = Context.t * Term.t * Term.typ


module Print (PP: Pretty_printer.SIG) =
struct
    module TP = Term_printer.Pretty (Gamma) (PP)

    let judgement ((c,term,typ): judgement): PP.t =
        TP.print Term.(Typed (term, typ)) (Context.gamma c)
end



let empty: context =
    Context.empty


let extract_context (c: context): Context.t =
    c

let extract_judgement (judge: judgement): Context.t * Term.t * Term.typ =
    judge





module Builder (Info: ANY) =
struct
    module Build = Build.Make (Info)

    type problem = Info.t * Type_error.t

    type 'a res = ('a, problem) result

    type t = Build.t -> Build.t res

    type tl = unit -> t

    type name = Info.t * string

    type formal_argument = name * tl

    type signature = formal_argument list * tl




    let binder (name: name) (typ: tl): t =
        fun bc ->
        let open Result in
        let open Build in
        map
            (start_binder name)
            (typ () (start_type bc))


    let make_type (typ: tl): t =
        fun bc ->
        let open Build in
        (typ () (start_type bc))


    let sort (info: Info.t) (s: Sort.t): t =
        Build.make_sort info s


    let variable (_: Info.t) (_: int): t =
        assert false


    let identifier (info: Info.t) (name: string): t =
        Build.make_identifier info name

    let unknown (_: Info.t): t =
        assert false

    let application (info: Info.t) (f: tl) (arg: tl): t =
        let open Result in
        fun bc ->
            Build.start_application bc
            |> f ()
            >>= fun bc ->
            Build.start_argument bc
            |> arg ()
            >>= fun bc ->
            Build.end_application info bc


    let lambda
            (_: Info.t) (_: name) (_: tl) (_: tl)
        : t
        =
        assert false

    let pi
            (info: Info.t) (name: name) (arg_typ: tl) (res_typ: tl)
        : t
        =
        fun bc ->
        let open Result in
        binder name arg_typ bc
        >>= (make_type res_typ)
        >>= Build.end_pi info


    let make_term (c: context) (term_builder: t): judgement res =
        Result.(
            map
                (fun bc ->
                     let t, typ = Build.get_final bc in
                     c, t, typ)
                (term_builder Build.(make c |> start_term)))


    let make_builtin
            (_: context)
            (_: name)
            (_: signature)
        : context res
        =
        assert false
end





module Check =
struct

    module Builder = Builder (Unit)

    type 'a res = ('a, Type_error.t) result


    let check_term (term: Term.t) (c: context): judgement res =
        let rec check term _ =
            let open Builder
            in
            match term with
            | Term.Sort s ->
                sort () s

            | Term.Appl (f, arg, _) ->
                application () (check f) (check arg)

            | Term.Lambda (argtp, exp, info) ->
                lambda
                    ()
                    ((), Term.Lambda_info.name info)
                    (check argtp)
                    (check exp)

            | _ ->
                assert false
    in
    Result.map_error
        snd
        (Builder.make_term c (check term ()))
end
