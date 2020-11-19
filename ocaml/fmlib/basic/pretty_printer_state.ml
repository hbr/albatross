module Text = Pretty_printer_text


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

type buffer = {
    ngroups: int;
    blength: int;
    groups: group Deque.t;
}


module Buffer =
struct
    let empty: buffer =
        {
            ngroups = 0;
            blength = 0;
            groups  = Deque.empty;
        }

    let count (b: buffer): int =
        b.ngroups

    let length (b: buffer): int =
        b.blength
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

    buffer: buffer;
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

        chunk ::= Break Text* group*
        group ::= group* chunk*


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


let enter_group (s: t): t =
    if s.active_groups < buffered_groups s then
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
                (* If nothing has been printed to the current line, then the
                 * [line_indent] has to be updated immediately. *)
                new_indent
            else
                s.line_indent;

        next_indent =
            if direct_out s then
                (* In direct output mode the new indentation must become
                 * immediately effective for the next line *)
                new_indent
            else
                s.next_indent;

    }
