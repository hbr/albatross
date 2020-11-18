open Common

module type PRETTY =
sig
    type t
    val has_more: t -> bool
    val peek: t -> char
    val advance: t -> t

    type doc

    val layout: int -> int -> doc -> t

    val empty: doc
    val string: string -> doc
    val substring: string -> int -> int -> doc
    val char: char -> doc
    val fill: int -> char -> doc
    val line: string -> doc
    val space: doc
    val cut: doc
    val nest: int -> doc -> doc
    val group: doc -> doc
    val (<+>): doc -> doc -> doc
    val chain: doc list -> doc
end




module Text  = Pretty_printer_text
module State = Pretty_printer_state






(* Readable
 * ========
 *
 * A pretty printer has to be a readable structure. I.e. we have to implement
 * all functions of a readable structure
 *)

module Readable =
struct
    type t =
        | Done
        | More of Text.t * State.t * (State.t -> t)



    let has_more (p: t): bool =
        match p with
        | Done ->
            false
        | _ ->
            true


    let peek (p: t): char =
        match p with
        | Done ->
            assert false (* Illegal call! *)

        | More (text, _, _) ->
            Text.peek text



    let advance (p: t): t =
        match p with
        | Done ->
            assert false (* Illegal call! *)

        | More (text, state, f) ->
            match Text.advance text with
            | None ->
                f state
            | Some text ->
                More (text, state, f)


    let next_text (p: t): (Text.t * t) option =
        match p with
        | Done ->
            None

        | More (text, state, f) ->
            Some (text, f state)

end

open Readable







(* Monad
 * =====
 *
 * The basis of the pretty printer is a continuation monad with a state. We need
 * the basic monadic operations [return] and [>>=] and functions to get, put and
 * update the state.
 *)


type 'a m = State.t -> ('a -> State.t -> t) -> t


let return (a: 'a): 'a m =
    fun s k -> k a s


let (>>=) (m: 'a m) (f: 'a -> 'b m): 'b m =
    fun s k ->
    m
        s
        (fun a s -> f a s k)


let get: State.t m =
    fun s k ->
    k s s


let put (s: State.t): unit m =
    fun _ k ->
    k () s


let update (f: State.t -> State.t): unit m =
    fun s k ->
    k () (f s)



(* Helper Functions
 * ================
 *)


let fill_aux (n: int) (c: char): unit m =
    assert (0 < n);
    fun s k ->
        assert (State.direct_out s);
        More (
            Text.fill n c,
            State.advance_position n s,
            k ())


let substring_aux (str: string) (start: int) (len: int): unit m =
    assert (0 <= start);
    assert (0 < len);
    assert (start + len <= String.length str);
    fun s k ->
    assert (State.direct_out s);
        More (
            Text.substring str start len,
            State.advance_position len s,
            k ()
        )


let char_aux (c: char): unit m =
    fun s k ->
        assert (State.direct_out s);
        More (
            Text.char c,
            State.advance_position 1 s,
            k ()
        )


let do_indent: unit m =
    get >>= fun s ->
    let n = State.line_indent s in
    if n = 0 then
        return ()
    else
        fill_aux n ' '


let line_aux: unit m =
    fun s k ->
    assert (State.line_direct_out s);
    More (
        Text.char '\n',
        State.newline s,
        k ()
    )









(* Document
 * ========
 *
 * The user is able to create and combine documents (see combinators below).
 *
 * At the end the user can layout a document i.e. convert it to a readable
 * structure.
 *)




type doc = unit m


let layout (width: int) (ribbon: int) (doc: doc): t =
    doc
        (State.init width ribbon)
        (fun () _ -> Done)









(* Generic combinators
 * ===================
 *)


let empty: doc =
    return ()



let (<+>) (doc1: doc) (doc2: doc): doc =
    doc1 >>= fun () -> doc2


let rec chain (lst: doc list): doc =
    match lst with
    | [] ->
        empty
    | hd :: tl ->
        hd >>= fun () -> chain tl


let rec separated_by (sep: doc) (lst: doc list): doc =
    match lst with
    | [] ->
        empty
    | [last] ->
        last
    | hd :: tl ->
        hd <+> sep
        >>=
        fun () -> separated_by sep tl



let nest (n: int) (doc: doc): doc =
    update (State.increment_indent n)
    <+>
    doc
    <+>
    update (State.increment_indent (-n))


let group (doc: doc): doc =
    update State.enter_group
    <+>
    doc
    <+>
    update State.leave_group





(* Specific Combinators
 * ====================
 *)


let substring (str: string) (start: int) (len: int): doc =
    assert (0 <= start);
    assert (start + len <= String.length str);
    if len = 0 then
        empty
    else
        get >>= fun s ->
        if State.direct_out s then
            do_indent <+> substring_aux str start len
        else
            assert false


let string (str: string): doc =
    substring str 0 (String.length str)


let fill (n: int) (c: char): doc =
    if n = 0 then
        empty
    else
        get >>= fun s ->
        if State.direct_out s then
            do_indent <+> fill_aux n c
        else
            assert false


let char (c: char): doc =
    get >>= fun s ->
    if State.direct_out s then
        do_indent <+> char_aux c
    else
        assert false


let line (_: string): doc =
    get >>= fun s ->
    if State.line_direct_out s then
        line_aux
    else
        assert false


let cut: doc =
    line ""


let space: doc =
    line " "


let wrap_words (s: string): doc =
    let word_start i =
        String.find (fun c -> c <> ' ') i s
    and word_end i =
        String.find (fun c -> c = ' ') i s
    and len =
        String.length s
    in
    let rec from start =
        let i = word_start start
        in
        if i = len then
            empty
        else
            let j = word_end i
            in
            let rest =
                substring s i (j - i)
                >>= fun () -> from j
            in
            if start < i then
                group space <+> rest
            else
                rest
    in
    from 0













(* Unit Tests
 * ==========
 *)


module From = String.From_readable (Readable)


let test
        (width: int) (ribbon: int) (print: bool)
        (doc: doc)
        (expected: string)
    : bool
    =
    let res =
        From.make (layout width ribbon doc)
    in
    if print then
        Printf.printf "\n%s\n" res;
    res = expected


let%test _ =
    let doc =
        string "line1"
        <+> cut
        <+> nest 4 (string "indented" <+> cut
                    <+> nest 4 (string "indented2" <+> cut)
                    <+> string "indented" <+> cut
                   )
        <+> string "line2"
    and expected =
        "line1\n\
        \    indented\n\
        \        indented2\n\
        \    indented\n\
        line2"
    in
    test 70 70 false doc expected
