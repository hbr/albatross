open Fmlib
open Common


type entry =
    | Global of int list
    | Local of int


type t =
    {map: entry String_map.t; has_locs: bool; cnt: int}


let empty: t =
    {map = String_map.empty; has_locs = false; cnt = 0}


let count (m:t): int =
    m.cnt


let has_locals (m: t): bool =
    m.has_locs




let find (name:string) (m:t): int list =
    match String_map.maybe_find name m.map with
    | None ->
        []
    | Some e ->
        match e with
        | Global lst ->
            lst
        | Local i ->
            [i]



let add_unnamed (m: t): t =
    { m with
        cnt = 1 + m.cnt;
    }


let add_global (name: string) (m: t): t =
    assert (name <> "");
    assert (not (has_locals m));
    if name = "_" then
        add_unnamed m
    else
    { m with
        map =
            String_map.add
                name
                (
                    match String_map.maybe_find name m.map with
                    | None ->
                        Global [ m.cnt ]
                    | Some (Global lst) ->
                        Global (m.cnt :: lst)
                    | _ ->
                        (* Cannot happen, because there are no locals. *)
                        assert false
                )
                m.map;

        cnt = 1 + m.cnt;
    }


let add_local (name: string) (m: t) : t =
    assert (name <> "");
    if name = "_" then
        add_unnamed m
    else
    {
        map = String_map.add name (Local m.cnt) m.map;

        has_locs = true;

        cnt = 1 + m.cnt;
    }
