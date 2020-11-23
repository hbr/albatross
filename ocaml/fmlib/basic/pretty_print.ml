open Common

module State  = Pretty_state
module Text   = State.Text
module Buffer = State.Buffer
module Group  = State.Group
module Chunk  = State.Chunk






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
end

include Readable







(* Monad
 * =====
 *
 * The basis of the pretty printer is a continuation monad with a state. We need
 * the basic monadic operations [return] and [>>=] and functions which operate
 * on the state. I.e. a state update and making decisions based on the context
 * of the state.
 *)


type 'a m = State.t -> ('a -> State.t -> t) -> t


let return (a: 'a): 'a m =
    fun s k -> k a s


let (>>=) (m: 'a m) (f: 'a -> 'b m): 'b m =
    fun s k ->
    m
        s
        (fun a s -> f a s k)


let (>=>) (f: 'a -> 'b m) (g: 'b -> 'c m): 'a -> 'c m =
    fun a s k ->
    f
        a
        s
        (fun b s -> g b s k)


let update (f: State.t -> State.t): unit m =
    fun s k ->
    k () (f s)



let update_and_get (f: State.t -> 'a * State.t): 'a m =
    fun s k ->
    let a, s = f s in
    k a s


let choice
        (p: State.t -> bool)
        (m1: unit -> 'a m)
        (m2: unit -> 'a m)
    : 'a m
    =
    fun s k ->
    if p s then
        m1 () s k
    else
        m2 () s k


let alternatives
        (lst: ((State.t -> bool) * (unit -> 'a m)) list)
        (otherwise: unit -> 'a m)
    : 'a m
    =
    let rec choose lst =
        fun s k ->
        match lst with
        | [] ->
            otherwise () s k
        | (p, m0) :: tail ->
            if p s then
                m0 () s k
            else
                choose tail s k
    in
    choose lst




(* Generate Output
 * ===============
 *
 * Fill the readable structure.
 *)


let print_text (text: Text.t) (): unit m =
    fun s k ->
    let indent =
        State.line_indent s
    and more s =
        More (
            text,
            State.advance_position (Text.length text) s,
            k ()
        )
    in
    if indent = 0 then
        more s
    else
        More (
            Text.fill indent ' ',
            State.advance_position indent s,
            more
        )


let print_line (): unit m =
    fun s k ->
    More (
        Text.char '\n',
        State.newline s,
        k ()
    )


let print_line_with_indent (indent: int) (): unit m =
    fun s k ->
    More (
        Text.char '\n',
        State.newline_with_indent indent s,
        k ()
    )









(* Flushing the Buffer
 * ===================
 *)


let rec flush_deque
        (f: 'a -> unit -> unit m)
        (deque: 'a Deque.t)
        ()
    : unit m
    =
    match Deque.pop_front deque with
    | None ->
        return ()
    | Some (e, deque) ->
        f e () >>= flush_deque f deque



let rec flush_flatten_group (g: Group.t) (): unit m =
    flush_deque
        flush_flatten_group
        (Group.complete_groups g)
        ()
    >>=
    flush_deque
        flush_flatten_chunk
        (Group.chunks g)


and flush_flatten_chunk (chunk: Chunk.t) (): unit m =
    print_text
        (Text.string (Chunk.break_text chunk))
        ()
    >>=
    flush_deque
        print_text
        (Chunk.texts chunk)
    >>=
    flush_deque
        flush_flatten_group
        (Chunk.groups chunk)



let flush_flatten (): unit m =
    update_and_get
        State.pull_buffer
    >>=
    fun buffer ->
    let rec flush buffer () =
        match Buffer.pop buffer with
        | None ->
            return ()
        | Some (group, buffer) ->
            flush_flatten_group group ()
            >>= flush buffer
            >>= fun () ->
            update State.flatten_done
    in
    flush buffer ()







let rec flush_effective_group (g: Group.t) (): unit m =
    (* All break hints belonging directly to the group are effective line
     * breaks. *)
    flush_deque
        flush_group
        (Group.complete_groups g)
        ()
    >>=
    flush_deque
        flush_effective_chunk
        (Group.chunks g)


and flush_effective_chunk (chunk: Chunk.t) (): unit m =
    (* The break hint starting the chunk is effective. *)
    print_line_with_indent
        (Chunk.indent chunk)
        ()
    >>=
    flush_deque
        print_text
        (Chunk.texts chunk)
    >>=
    flush_deque
        flush_group
        (Chunk.groups chunk)


and flush_group (g: Group.t) (): unit m =
     choice
         (State.fits (Group.length g))
         (flush_flatten_group g)
         (flush_effective_group g)



let flush_effective (): unit m =
    update_and_get
        State.pull_buffer
    >>=
    fun buffer ->
    let rec flush buffer nflushed () =
        let flush_done () =
            update (State.effective_done buffer nflushed)
        in
        choice
            (State.fits (Buffer.length buffer))
            flush_done
            (fun () ->
             match Buffer.pop buffer with
             | None ->
                 flush_done ()
             | Some (group, buffer) ->
                 flush_effective_group group ()
                 >>=
                 flush buffer (nflushed + 1)
            )
    in
    flush buffer 0 ()








(* Print or Push Text and Break Hints
 * ==================================
 *)


let update_and_flush (f: State.t -> State.t) (): unit m =
    update f
    >>=
    fun _ ->
    choice
        State.buffer_fits
        return
        flush_effective


let put_text (text: Text.t): unit m =
    choice
        State.direct_out
        (print_text text)
        (update_and_flush (State.push_text text))


let rec put_line (str: string) (): unit m =
    alternatives
        [
            State.line_direct_out,
            print_line;

            State.within_active,
            (update_and_flush (State.push_break str))
        ]
        (flush_flatten >=> put_line str)







(* Document
 * ========
 *
 * The user is able to create and combine documents.
 *
 * At the end the user can layout a document i.e. convert it to a readable
 * structure.
 *)




type doc = unit m


let layout (width: int) (ribbon: int) (doc: doc): t =
    (doc >>= flush_flatten)
        (State.init width ribbon)
        (fun () _ -> Done)



let empty: doc =
    return ()



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


let line (str: string): doc =
    put_line str ()











(* Generic combinators
 * ===================
 *)


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







(* Convenience Combinators
 * =======================
 *)


let cut: doc =
    line ""


let space: doc =
    line " "


let pack (break: string) (lst: doc list): doc =
    separated_by (group (line break)) lst


let stack (break: string) (lst: doc list): doc =
    group (separated_by (line break) lst)


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


let test0
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


let test (width: int) (print: bool) (doc: doc) (expected: string): bool =
    test0 width width print doc expected


let string_list (lst: string list): doc list =
    List.map string lst

let _ = string_list



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
    test 70 false doc expected



let%test _ =
    let doc =
        pack " " (string_list ["0"; "1"])
    and expected =
        "0 1"
    and width =
        3
    in
    test width false doc expected


let%test _ =
    let doc =
        pack " " (string_list ["0"; "1"])
    and expected =
        "0\n1"
    and width =
        2
    in
    test width false doc expected


let%test _ =
    let doc =
        pack " " (string_list ["0"; "1"; "ab"; "cd"; "3"; "4"])
    and expected =
        "0 1\nab\ncd\n3 4"
    and width =
        3
    in
    test width false doc expected


let%test _ =
    let doc =
        pack
            " "
            [char '0'; nest 2 (char '1'); char '2']
    and expected =
        "0\n  1\n2"
    in
    test 2 false doc expected


let%test _ =
    let doc =
        wrap_words "0 1 ab cd"
    and expected =
        "0 1\n\
         ab\n\
         cd"
    in
    test 3 false doc expected










(* Unit Tests with Trees
 * ---------------------
 *)

type tree =
    { name: string; children: tree list; }


let leaf (name: string): tree =
    {name; children = []}

let tree (name: string) (children: tree list): tree =
    {name; children}


let tree0 () =
    tree "ff" [leaf "a"; leaf "b"; leaf "c"]

let tree1 () =
    tree
        "ff"
        [leaf "a";
         tree "gf" [leaf "b"; leaf "c"];
         leaf "d"]

let _ = tree0
let _ = tree1


let doc_tree (tree: tree): doc =
    let rec doc is_top tree =
        match tree.children with
        | [] ->
            string tree.name
        | _ ->
            let d =
                string tree.name <+> space
                <+>
                nest
                    2
                    (stack
                         " "
                         (List.map (doc false) tree.children))
            in
            group (
                if is_top then
                    d
                else
                    char '(' <+> d <+> char ')'
            )
    in
    doc true tree



let%test _ =
    let doc =
        doc_tree (tree1 ())
    and expected =
        "ff a (gf b c) d"
    in
    test 80 false doc expected



let%test _ =
    let doc =
        doc_tree (tree0 ())
    and expected =
        "ff\n  a\n  b\n  c"
    in
    test 3 false doc expected


let%test _ =
    let doc =
        doc_tree (tree0 ())
    and expected =
        "ff\n  a b c"
    in
    test 7 false doc expected


let%test _ =
    let doc =
        doc_tree (tree1 ())
    and expected =
        "ff\n  a\n  (gf b c)\n  d"
    in
    test 10 false doc expected


let%test _ =
    let doc =
        doc_tree (tree1 ())
    and expected =
        "ff\n  a\n  (gf\n    b c)\n  d"
    in
    test 8 false doc expected
