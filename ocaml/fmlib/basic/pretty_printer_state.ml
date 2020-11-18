type t = {
    width: int;
    ribbon: int;

    position: int;       (* Current position on the line *)

    line_indent: int;    (* Anything inserted at position 0 has to be
                            indented this amount. *)
    current_indent: int; (* The current indentation level *)


    active_groups: int;    (* Number of open active groups *)
    effective_groups: int; (* Number of open effective groups *)
    right_groups: int;     (* Number of open groups to the right of the last
                              open group in the buffer *)
}

let init (width: int) (ribbon: int): t =
    {
        width;
        ribbon;

        position = 0;

        line_indent = 0;
        current_indent = 0;

        active_groups = 0;
        effective_groups = 0;
        right_groups = 0;
    }


let line_indent (s: t): int =
    if s.position = 0 then
        s.line_indent
    else
        0


let advance_position (n: int) (s: t): t =
    {s with position = s.position + n}


let newline (s: t): t =
    {s with position = 0}


let direct_out (_: t): bool =
    true

let line_direct_out (_: t): bool =
    true


let increment_indent (n: int) (s: t): t =
    let new_indent = s.current_indent + n
    in
    {s with
     current_indent =
         new_indent;
     line_indent =
         if direct_out s then
             new_indent
         else
             s.line_indent
    }


let buffered_groups (_: t): int =
    assert false


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
