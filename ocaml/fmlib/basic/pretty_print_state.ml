module Text = Pretty_print_text


type
    chunk = {
        break_text:
            string;

        indent:             (* Indentation level at the first text block. *)
            int;

        texts:
            Text.t Deque.t;

        chunk_groups:
            group Deque.t;
    }

and
    group = {
        glength: int;
        complete_groups: group Deque.t;
        chunks: chunk Deque.t;
    }




module Chunk =
struct
    type t = chunk

    let make (break_text: string) (indent: int): t =
        {
            break_text;
            indent;
            texts = Deque.empty;
            chunk_groups = Deque.empty;
        }

    let push_text (text: Text.t) (chunk: t): t =
        (* If the chunk has already groups, no more text can be added. *)
        assert (Deque.is_empty chunk.chunk_groups);
        {
            chunk with
            texts =
                Deque.push_rear
                    text
                    chunk.texts
        }

    let add_group (group: group) (chunk: t): t =
        {
            chunk with
            chunk_groups =
                Deque.push_rear
                    group
                    chunk.chunk_groups;
        }


    let break_text (chunk: t): string =
        chunk.break_text


    let indent (chunk: t): int =
        chunk.indent


    let texts (chunk: t): Text.t Deque.t =
        chunk.texts


    let groups (chunk: t): group Deque.t =
        chunk.chunk_groups
end



module Group =
struct
    type t = group

    let push_text (text: Text.t) (group: t): t =
        (* Text can only be pushed to a group if it has at least one chunk. *)
        assert (not (Deque.is_empty group.chunks));
        {
            group with
            chunks =
                Deque.update_last
                    (Chunk.push_text text)
                    group.chunks;
            glength =
                group.glength + Text.length text;
        }


    let length (group: t): int =
        group.glength


    let complete_groups (group: t): t Deque.t =
        group.complete_groups


    let chunks (group: t): Chunk.t Deque.t =
        group.chunks
end



module Buffer =
struct
    type t = {
        ngroups: int;
        length: int;
        groups: group list;
    }


    let empty: t =
        {
            ngroups = 0;
            length = 0;
            groups  = [];
        }


    let count (b: t): int =
        b.ngroups


    let length (b: t): int =
        b.length


    let push_text (text: Text.t) (b: t): t =
        match b.groups with
        | hd :: tl ->
            {
                b with
                groups =
                    (Group.push_text text hd) :: tl;
                length =
                    b.length + Text.length text;
            }
        | _ ->
            assert false (* Illegal call: Before text can be pushed, at least a
                            line break has to be pushed, i.e. the buffer cannot
                            be empty. *)


    let reverse (b: t): t =
        {b with groups = List.rev b.groups}

    let groups (b: t): Group.t list =
        b.groups

    let pop (b: t): (Group.t * t) option =
        match b.groups with
        | [] ->
            None
        | g :: groups ->
            let len = Group.length g in
            assert (len <= b.length);
            Some (
                g,
                {ngroups = b.ngroups - 1;
                 length  = b.length - len;
                 groups }
            )
end





type t = {
    width: int;
    ribbon: int;

    position: int;       (* Current position on the line *)

    line_indent: int;    (* Anything inserted at position 0 has to be
                            indented this amount. *)
    next_indent: int;    (* Indentation of the next line. *)
    current_indent: int; (* The current indentation level *)


    active_groups: int;    (* Number of open active groups *)
    effective_groups: int; (* Number of open effective groups *)
    right_groups: int;     (* Number of open groups to the right of the last
                              open group in the buffer *)

    buffer: Buffer.t;
}


let init (width: int) (ribbon: int): t =
    {
        width;
        ribbon;

        position = 0;

        line_indent = 0;
        next_indent = 0;
        current_indent = 0;

        active_groups = 0;
        effective_groups = 0;
        right_groups = 0;

        buffer = Buffer.empty
    }


let line_indent (s: t): int =
    if s.position = 0 then
        s.line_indent
    else
        0


let advance_position (n: int) (s: t): t =
    assert ( s.position <> 0
             ||
             s.line_indent <= n);
    (* Positions between 0 and line_indent are illegal. *)
    {s with position = s.position + n}


let newline (s: t): t =
    {s with position = 0; line_indent = s.next_indent;}


let newline_with_indent (indent: int) (s: t): t =
    {s with
     position = 0;
     line_indent = indent;
     next_indent = indent}



let fits (n: int) (s: t): bool =
    (* Is it possible to put [n] more characters on the current line without
     * violating the line width and the ribbon size? *)
    if s.position = 0 then
        n <= s.ribbon
        &&
        s.line_indent + n <= s.width
    else
        begin
            assert (s.line_indent <= s.position);
            s.position - s.line_indent + n <= s.ribbon
            &&
            s.position + n <= s.width
        end







(* Groups and Buffering
 * ====================


    There is a time lag between the opening and closing of a group by the user
    and the opening and closing of groups in the buffer.

    A group in the buffer is opened at the first break hint in that group. All
    text before the first break hint belongs is placed before the group.

    A group in the buffer is closed at the first break hint after the group has
    been closed by the user. All text before the first break hint after the user
    closing the group still belongs to that group.


    Grammar of the buffer content:

        buffer  ::= igroups                 -- outermost to innermost

        igroup  ::= { groups chunks         -- incomplete group

        chunk   ::= break texts groups

        group   ::= { groups chunks }       -- '{' start of group, '}' end of
                                            -- group

   Invariant:

        - The sum of `effective_groups`, `active_groups` and `right_groups` is
        only incremented by `open_group` and decremented by `close_group`.

        - The `active_groups` can only be incremented as long as the buffer is
        empty. If the buffer is not empty, they can be decremented. `open_group`
        increments the `right_groups` if there is a non empty buffer.

        - Every line break in buffering mode creates a new chunk with a break
        hint only and either appends this chunk to some incomplete group or
        makes a new incomplete group with this chunk.

        - The groups in the buffer are never empty. At the start of buffering we
        have an innermost incomplete group with a line break only chunk and all
        the outer incomplete groups contain at innermost group directly or
        indirectly. A complete group is only generated from an incomplete group
        and is therefore nonempty as well.

        - The last incomplete group in the buffer has at least one chunk at the
        end.

        - Any complete group in the buffer (either at the end of a chunk or at
        the start of an incomplete group) is immediately followed by a break
        hint. Reason: Groups are completed only if a break hint is entered into
        the buffer. The chunk with the break hint immediately follows the
        completed group.

        - Break hints can be put into the buffer only if there is at least one
        active group. Reason: If there is no active group then the break hint
        marks the end of the active region and causes the buffer to be flushed
        flattened.


    Start of buffering:

        There are open active groups and the first break hint with one of the
        active groups arrive.

        We have to open all active groups in the buffer. All outer active groups
        are empty, only the innermost has the break hint and nothing else.

   Text during buffering:

        Is always appended to the last chunk of the last opened group.

   Break hint during buffering within open active groups:

        a) More open active groups than groups in the buffer:

            Append new groups in the buffer and put a chunk with the break hint
            to the last group in the buffer.

        b) The same number of active groups as groups in the buffer:

            Add a new chunk to the last group in the buffer

        c) Fewer active groups (but still some) than groups in the buffer:

            Close the corresponging groups in the buffer and append them to the
            last chunk of the parent group or to the completed groups of the
            parent group. Add a new chunk to the last group in the buffer.

    Break hint during buffering outside active groups:

        Buffer has to be flushed as flattened and then it has to be checked
        whether the break hint starts buffering again.


 *)


let buffered_groups (s: t): int =
    (* Number of open groups in the buffer. *)
    Buffer.count s.buffer


let is_buffering (s: t): bool =
    0 < buffered_groups s


let direct_out (s: t): bool =
    not (is_buffering s)


let line_direct_out (s: t): bool =
    direct_out s
    &&
    s.active_groups = 0


let within_active (s: t): bool =
    0 < s.active_groups


let buffer_fits (s: t): bool =
    fits (Buffer.length s.buffer) s



let push_text (_: Text.t) (s: t): t =
    assert (is_buffering s);
    assert false



let push_break (_: string) (s: t): t =
    assert (within_active s);
    let oa = s.active_groups
    and nbuf = buffered_groups s
    in
    if nbuf < oa then
        assert false
    else if nbuf = oa then
        assert false
    else
        assert false


let pull_buffer (s: t): Buffer.t * t =
    Buffer.reverse s.buffer,
    {s with buffer = Buffer.empty}


let push_buffer (_: Buffer.t) (s: t): t =
    assert (direct_out s);
    assert false



let enter_group (s: t): t =
    if is_buffering s then
        {s with right_groups = s.right_groups + 1}
    else
        {s with active_groups = s.active_groups + 1}


let leave_group (s: t): t =
    if 0 < s.right_groups then
        {s with right_groups = s.right_groups - 1}
    else if 0 < s.active_groups then
        {s with active_groups = s.active_groups - 1}
    else
        begin
            assert (0 < s.effective_groups);
            {s with effective_groups = s.effective_groups - 1}
        end






(* Indenting
 * =========
 *)

let increment_indent (n: int) (s: t): t =
    let new_indent =
        s.current_indent + n
    in
    {
        s with

        current_indent =
            new_indent;

        line_indent =
            if s.position = 0 then
                (* Nothing has been printed to the current line. The
                 * [line_indent] has to be updated immediately. *)
                new_indent
            else
                s.line_indent;

        next_indent =
            if direct_out s then
                (* In direct output mode the new indentation must become
                 * effective for the next line *)
                new_indent
            else
                s.next_indent;

    }
