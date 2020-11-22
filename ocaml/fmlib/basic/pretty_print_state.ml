open Common

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

    let push_text (text: Text.t) (indent: int) (chunk: t): t =
        (* If the chunk has already groups, no more text can be added. *)
        assert (Deque.is_empty chunk.chunk_groups);
        {
            chunk with

            indent =
                if Deque.is_empty chunk.texts then
                    indent
                else
                    chunk.indent;

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

    let empty: t =
        {
            glength = 0;
            complete_groups = Deque.empty;
            chunks = Deque.empty;
        }


    let make (str: string) (indent: int): t =
        {
            glength = String.length str;
            complete_groups = Deque.empty;
            chunks = Deque.(empty |> push_rear (Chunk.make str indent));
        }


    let push_text (text: Text.t) (indent: int) (group: t): t =
        (* Text can only be pushed to a group if it has at least one chunk. *)
        assert (not (Deque.is_empty group.chunks));
        {
            group with
            chunks =
                Deque.update_last
                    (Chunk.push_text text indent)
                    group.chunks;
            glength =
                group.glength + Text.length text;
        }

    let push_break (str: string) (indent: int) (group: t): t =
        {
            group with

            chunks =
                Deque.push_rear
                    (Chunk.make str indent)
                    group.chunks;

            glength =
                group.glength + String.length str;
        }


    let add_complete (complete_group: t) (group: t): t =
        if Deque.is_empty group.chunks then
            {
                group with

                complete_groups =
                    Deque.push_rear
                        complete_group
                        group.complete_groups;
            }
        else
            {
                group with

                chunks =
                    Deque.update_last
                        (Chunk.add_group complete_group)
                        group.chunks;
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


    let is_empty (b: t): bool =
        b.ngroups = 0


    let length (b: t): int =
        b.length


    let push_text (text: Text.t) (indent: int) (buffer: t): t =
        assert (0 < count buffer);
        let hd, tl =
            List.split_head_tail buffer.groups
        in
        {
            buffer with

            groups =
                (Group.push_text text indent hd) :: tl;

            length =
                buffer.length + Text.length text;
        }


    let push_break (str: string) (indent: int) (b: t): t =
        assert (0 < count b);
        let hd, tl =
            List.split_head_tail b.groups
        in
        {
            b with

            groups =
                (Group.push_break str indent hd) :: tl;

            length =
                b.length + String.length str
        }


    let close_one (buffer: t): t =
        match buffer.groups with
        | last :: previous :: groups ->
            {
                buffer with

                groups =
                    Group.add_complete last previous :: groups
            }
        | _ ->
            assert false (* Illegal call! *)


    let close_and_open
            (nclose: int)
            (nopen: int)
            (str: string)
            (indent: int)
            (buffer: t)
        : t
        =
        assert (nclose = 0 || nclose < count buffer);
        assert (0 < nopen);
        let buffer =
            Int.iterate nclose close_one buffer
        in
        {
            ngroups =
                buffer.ngroups - nclose + nopen;

            length =
                buffer.length + String.length str;

            groups =
                Group.make str indent
                ::
                Int.iterate
                    (nopen - 1)
                    (fun gs -> Group.empty :: gs)
                    buffer.groups;
        }



    let reverse (b: t): t =
        {b with groups = List.rev b.groups}


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
        empty. If the buffer is not empty, they can only be decremented.
        `open_group` increments the `right_groups` if there is a non empty
        buffer.

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



let push_text (text: Text.t) (s: t): t =
    assert (is_buffering s);
    {s with
     buffer = Buffer.push_text text s.current_indent s.buffer}



let push_break (str: string) (s: t): t =
    assert (within_active s);
    let oa = s.active_groups
    and nbuf = buffered_groups s
    in
    if nbuf = 0 then
        (* Start buffering *)
        { s with
          buffer =
              Buffer.close_and_open
                  0
                  oa
                  str
                  s.current_indent
                  s.buffer
        }
    else if oa < nbuf then
        (* The innermost [nbuf - oa] groups in the buffer have already been
         * closed by the user. We close these groups in the buffer as well and
         * open [right_groups] in the buffer there the last group has a chunk
         * with the break hint. *)
        {
            s with
            right_groups =
                0;
            active_groups =
                oa + s.right_groups;
            buffer =
                Buffer.close_and_open
                    (nbuf - oa)
                    s.right_groups
                    str
                    s.current_indent
                    s.buffer;
        }
    else if oa = nbuf then
        (* The innermost group in the buffer is still open. We add a new chunk
         * with this break hint to the innermost group. *)
        {
            s with

            buffer =
                Buffer.push_break str s.current_indent s.buffer;
        }
    else
        (* nbuf < oa *)
        assert false (* This case cannot happen. At the start of buffering we
                        have [nbuf = oa]. If more groups are opened, they are
                        all counted as [right_groups]. *)



let pull_buffer (s: t): Buffer.t * t =
    Buffer.reverse s.buffer,
    {s with buffer = Buffer.empty}



let flatten_done (s: t): t =
    (* The complete buffer has been flattened. *)
    assert (not (is_buffering s));
    assert (s.active_groups = 0);
    {
        s with
         active_groups = s.right_groups;
         right_groups  = 0;
    }



let effective_done (buffer: Buffer.t) (nflushed: int) (s: t): t =
    (* The outermost [nflushed] groups have been flushed as effective groups.
       Now the buffer fits.
     *)
    assert (not (is_buffering s));
    assert (Buffer.is_empty buffer || fits (Buffer.length buffer) s);
    let buffer =
        Buffer.reverse buffer
    and nflushed =
        min nflushed s.active_groups (* Of the flushed groups, only the groups
                                        count which had been open initially. *)
    in
    let effective_groups, active_groups, right_groups =
        if Buffer.count buffer = 0 then
            (* All groups have been flushed, buffer is empty. *)
            begin
                s.effective_groups + nflushed,
                s.active_groups + s.right_groups - nflushed,
                0
            end
        else if 0 < s.active_groups then
            s.effective_groups + nflushed,
            s.active_groups    - nflushed,
            s.right_groups
        else
            begin
                assert (s.active_groups = 0);
                assert (nflushed = 0);
                s.effective_groups,
                s.right_groups,
                0
            end
    in
    {
        s with buffer; effective_groups; active_groups; right_groups;
    }







(* Enter and Leave Groups
 * ======================
 *)

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
