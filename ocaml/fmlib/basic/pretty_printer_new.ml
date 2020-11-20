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







(* Generate Output
 * ===============
 *)


let print_text (text: Text.t): unit m =
    fun s k ->
    More (
        text,
        State.advance_position (Text.length text) s,
        k ()
    )


let print_indent: unit m =
    get >>= fun s ->
    let n = State.line_indent s in
    if n = 0 then
        return ()
    else
        print_text (Text.fill n ' ')


let print_line: unit m =
    fun s k ->
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







(* Flushing the Buffer
 * ===================

    1. Buffer fits and active region ended:

        Flush the complete buffer flattened. The outermost buffered group has
        been ended and fits completely. Therefore all inner groups fit
        completely i.e. the whole buffer can be flushed as flattened.


    2. The buffer does not fit:

        The outermost group in the buffer must be effective. The inner groups
        can still be flattened or effective.

        All completed groups within the outermost group fit. Otherwise they
        wouldn't had been completed. Therefore the completed groups in the
        outermost groups can be printed as flattened.

        After the outermost buffered group printed as effective, the remaining
        buffer might still be too large. I.e. the process of printing the
        outermost buffered group as effective must be continued until the buffer
        fits (or is empty).

 *)



let flush_flatten (): unit m =
    assert false


let flush_one_effective (): bool m =
    get >>= fun s ->
    if State.buffer_fits s then
        return true
    else
        assert false


let rec flush_effective (): unit m =
    flush_one_effective ()
    >>=
    fun ok ->
    if ok then
        return ()
    else
        flush_effective ()







(* Elementary Combinators
 * ======================
 *)


let put_text (text: Text.t): doc =
    get >>= fun s ->
    if State.direct_out s then
        print_indent <+> print_text text
    else
        (* We are buffering! *)
        let s = State.push_text text s in
        if State.buffer_fits s then
            put s
        else
            assert false



let rec line (str: string): doc =
    get
    >>=
    fun s ->
    if State.line_direct_out s then
        print_line

    else if State.within_active s then
        let s = State.push_break str s in
        if State.buffer_fits s then
            put s
        else
            put s
            >>=
            flush_effective

    else
        put s
        >>=
        flush_flatten
        >>=
        fun _ ->
        line str



let substring (str: string) (start: int) (len: int): doc =
    assert (0 <= start);
    assert (start + len <= String.length str);
    if len = 0 then
        empty
    else
        put_text (Text.substring str start len)


let string (str: string): doc =
    substring str 0 (String.length str)


let fill (n: int) (c: char): doc =
    if n = 0 then
        empty
    else
        put_text (Text.fill n c)


let char (c: char): doc =
    put_text (Text.char c)








(* Convenience Combinators
 * =======================
 *)


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
