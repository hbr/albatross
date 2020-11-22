(* A text block is never empty. *)
type t =
    | String of string * int * int
    | Fill of int * char


let substring (str: string) (start: int) (len: int): t =
    assert (0 <= start);
    assert (0 < len);
    assert (start + len <= String.length str);
    String (str, start, len)


let string (str: string): t =
    let len = String.length str in
    assert (0 < len);
    substring str 0 len


let fill (n: int) (c: char): t =
    assert (0 < n);
    Fill (n, c)

let char (c: char): t =
    Fill (1, c)


let length: t -> int = function
    | String (_, _, len) ->
        len
    | Fill (len, _) ->
        len


let peek (text: t): char =
    match text with
    | String (s, start, _) ->
        assert (start < String.length s);
        s.[start]
    | Fill (_, c) ->
        c


let advance (text: t): t option =
    match text with
    | String (s, start, len) ->
        if 1 < len then
            Some (String (s, start + 1, len - 1))
        else
            None
    | Fill (len, c) ->
        if 1 < len then
            Some (Fill (len - 1, c))
        else
            None
