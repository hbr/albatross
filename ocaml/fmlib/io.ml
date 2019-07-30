open Common_module_types
open Common


module type STAT =
  sig
    type t
    type time

    val compare: time -> time -> int
    val is_directory: t -> bool
    val is_file:      t -> bool
    val modification: t -> time
  end


module type BUFFER =
  sig
    type t
    val alloc: int -> t
  end




module type BUFFERS =
  functor (B:BUFFER) ->
  sig
    type t
    val make: int -> t
    val is_open_read: t -> int -> bool
    val is_open_write: t -> int -> bool
    val capacity: t -> int
    val occupy_readable: t -> int -> int
    val occupy_writable: t -> int -> int
    val release: t -> int -> unit
    val readable_file: t -> int -> int * B.t
    val writable_file: t -> int -> int * B.t
    val find_open: t -> int -> int
  end








module Buffers: BUFFERS =
  functor (B:BUFFER) ->
  struct
    type file =
      | Read  of int * B.t
      | Write of int * B.t


    type t = {size: int;
              files: file Pool.t}

    let make (size:int): t =
      {size;
       files = Pool.make_empty ()}

    let is_open (s:t) (i:int): bool =
      Pool.has s.files i

    let is_open_read (s:t) (i:int): bool =
      Pool.has s.files i
      && match Pool.elem s.files i with
         | Read _  -> true
         | Write _ -> false

    let is_open_write (s:t) (i:int): bool =
      Pool.has s.files i
      && match Pool.elem s.files i with
         | Read _  -> false
         | Write _ -> true

    let capacity (s:t): int =
      Pool.capacity s.files

    let occupy (s:t) (f:B.t -> file): int =
      let buf = B.alloc s.size in
      Pool.occupy s.files (f buf)

    let occupy_readable (s:t) (fd:int): int =
      occupy s (fun b -> Read(fd,b))

    let occupy_writable (s:t) (fd:int): int =
      occupy s (fun b -> Write(fd,b))

    let release (s:t) (i:int): unit =
      assert (is_open s i);
      Pool.release s.files i

    let readable_file (s:t) (i:int): int * B.t =
      match Pool.elem s.files i with
      | Read (fd,b) -> fd,b
      | Write _ -> assert false (* Illegal call! *)

    let writable_file (s:t) (i:int): int * B.t =
      match Pool.elem s.files i with
      | Read _ -> assert false (* Illegal call! *)
      | Write (fd,b) -> fd,b

    let find_open (s:t) (i:int): int =
      assert (i <= Pool.capacity s.files);
      Pool.find s.files i
  end (* Buffers *)







module type SIG_MIN =
  sig
    type in_file
    type out_file

    val stdin:  in_file
    val stdout: out_file
    val stderr: out_file

    module M: MONAD
    include MONAD

    module Process:
    sig
      val exit: int -> 'a t
      val execute: unit t -> unit
      val command_line: string array t
      val current_working_directory: string  t
    end

    module Path0:
    sig
      val separator: char
      val delimiter: char
    end

    val read_directory: string -> string array option t

    val prompt: string -> string option t

    (*val open_for_read:  string -> in_file  option t
    val open_for_write: string -> out_file option t
    val create: string -> out_file option t
    val close_in:  in_file  -> unit t
    val close_out: out_file -> unit t
    val flush: out_file -> unit t
    val flush_all: unit t

    val getc: in_file -> char option t
    val putc: char -> out_file  ->  unit t
    val get_line: in_file -> string option t
    val put_substring: string -> int -> int -> out_file -> unit t*)

    module Read: functor (W:WRITABLE) ->
                 sig
                   val read_buffer: in_file -> W.t -> W.t t
                   val read: in_file -> W.t -> W.t t
                 end
    module Write: functor (R:READABLE) ->
                  sig
                    val write_buffer: out_file -> R.t -> R.t t
                    val write: out_file -> R.t -> R.t t
                  end
  end






module type SIG =
  sig
    include SIG_MIN

    module Path:
    sig
      val absolute: string -> string t
      val split: string -> (string * string) option
      val normalize: string -> string
      val join: string -> string -> string
    end

    module Directory:
    sig
      val read: string -> string array option t
    end

    (*val read_file:   string -> 'a t -> (in_file  -> 'a t) -> 'a t
    val write_file:  string -> 'a t -> (out_file -> 'a t) -> 'a t
    val create_file: string -> 'a t -> (out_file -> 'a t) -> 'a t*)

    module File:
    sig
      module In:
      sig
        type fd
      end
      module Out:
      sig
        type fd
        val putc: char -> fd -> unit t
        val substring: string -> int -> int -> fd -> unit t
        val string: string -> fd -> unit t
        val line: string -> fd -> unit t
        val newline: fd -> unit t
        val fill: int -> char -> fd -> unit t
      end
      val stdin:  In.fd
      val stdout: Out.fd
      val stderr: Out.fd
    end

    module Repl:
    sig
      val prompt: string -> string option t
    end


    (*val getc_in: char option t
    val get_line_in: string option t*)

    module Stdout:
    sig
      val putc: char -> unit t
      val string: string -> unit t
      val line: string -> unit t
      val newline: unit t
      val fill: int -> char -> unit t
    end

    module Stderr:
    sig
      val putc: char -> unit t
      val string: string -> unit t
      val line: string -> unit t
      val newline: unit t
      val fill: int -> char -> unit t
    end
  end


let path_split (sep:char) (path:string): (string * string) option =
  let len = String.length path
  in
  let len =
    if 2 <= len && path.[len-1] = sep then
      len - 1
    else
      len
  in
  let pos = String.find_bwd (fun c -> c = sep) len path
  in
  if pos = -1 || (pos = 0 && len = 1) then
    None
  else
    let basename = String.sub path (pos+1) (len-pos-1)
    and dirname =
      if pos = 0 then
        String.one sep
      else
        String.sub path 0 pos
    in
    Some (dirname, basename)

let print_split sep path =
  match path_split sep path with
  | None ->
     Printf.printf "split %s = None\n" path
  | Some(d,b) ->
     Printf.printf "split %s = (%s, %s)\n" path d b
let _ = print_split

let%test _ =
  path_split '/' "" = None

let%test _ =
  path_split '/' "/" = None

let%test _ =
  path_split '/' "/hello" = Some ("/", "hello")

let%test _ =
  path_split '/' "/User/name/xxx" = Some ("/User/name", "xxx")

let%test _ =
  path_split '/' "/User/name/xxx/" = Some ("/User/name", "xxx")



let path_normalize (sep:char) (path:string): string =
  (* remove duplicate separators and normalize "." and ".." *)
  let rec norm lst nlst =
    match lst with
    | [] ->
       String.concat (String.one sep) (List.rev nlst)
    | "" :: tl ->
       if nlst = [] || tl = [] then
         norm tl ("" :: nlst)
       else
         norm tl nlst
    | "." :: tl ->
       norm tl nlst
    | h :: _ :: ".." :: tl ->
       norm (h :: tl) nlst
    | _ :: ".." :: tl ->
       norm tl nlst
    | h :: tl ->
       norm tl (h :: nlst)
  in
  if String.length path = 0 then
    "."
  else
    norm (String.split_on_char sep path) []

let%test _ =
  path_normalize '/' "/" = "/"

let%test _ =
  path_normalize '/' "//" = "/"

let%test _ =
  path_normalize '/' "" = "."

let%test _ =
  path_normalize '/' "abc/def/ghi" = "abc/def/ghi"

let%test _ =
  path_normalize '/' "abc/" = "abc/"

let%test _ =
  path_normalize '/' "abc/def///ghi" = "abc/def/ghi"

let%test _ =
  path_normalize '/' "abc/./def" = "abc/def"

let%test _ =
  path_normalize '/' "a/../b" = "b"

let%test _ =
  path_normalize '/' "../a" = "../a"

let%test _ =
  path_normalize '/' "a/b/../../d" = "d"







module Make (M:SIG_MIN): SIG =
  struct
    include M

    module Path =
      struct
        let absolute (path:string): string t =
          let len = String.length path
          in
          if 0 < len && path.[0] = Path0.separator then
            return path
          else
            Process.current_working_directory >>= fun cwd ->
            return (if len = 0
                    then cwd
                    else cwd ^ String.one Path0.separator ^ path)

        let split (path:string): (string * string) option =
          path_split Path0.separator path

        let normalize (path:string): string =
          path_normalize Path0.separator path

        let join (dir:string) (base:string): string =
          dir ^ String.one Path0.separator ^ base
      end

    module Directory =
      struct
        let read = read_directory
      end


    (*let read_file
          (path:string) (cannot_open:'a t) (read:in_file -> 'a t)
        : 'a t =
      open_for_read path >>= fun fd ->
      match fd with
      | None ->
         cannot_open
      | Some fd ->
         read fd >>= fun a ->
         close_in fd >>= fun _ ->
         return a

    let write_file
          (path:string) (cannot_open:'a t) (write:out_file -> 'a t)
        : 'a t =
      open_for_write path >>= fun fd ->
      match fd with
      | None ->
         cannot_open
      | Some fd ->
         write fd >>= fun a ->
         close_out fd >>= fun _ ->
         return a

    let create_file
          (path:string) (cannot_create:'a t) (write:out_file -> 'a t): 'a t =
      create path >>= fun fd ->
      match fd with
      | None ->
         cannot_create
      | Some fd ->
         write fd >>= fun a ->
         close_out fd >>= fun _ ->
         return a
     *)

    module File =
      struct
        module In =
          struct
            type fd = in_file
          end
        module Out =
          struct
            type fd = out_file
            let substring
                  (s:string) (start:int) (len:int) (fd:out_file)
                : unit t =
              let module W = Write (String_reader) in
              W.write fd (String_reader.of_substring s start len)
              >>= fun _ ->
              return ()

            let string (s:string) (fd:out_file): unit t =
              substring s 0 (String.length s) fd

            let putc (c:char) (fd:out_file): unit t =
              let module W = Write (Char_reader) in
              W.write fd (Char_reader.make c)
              >>= fun _ ->
              return ()

            let newline (fd:out_file): unit t =
              putc '\n' fd

            let line (s:string) (fd:out_file): unit t =
              string s fd >>= fun _ ->
              newline fd

            let fill (n:int) (c:char) (fd:out_file): unit t =
              let module W = Write (Fill_reader) in
              W.write fd (Fill_reader.make n c)
              >>= fun _ ->
              return ()
          end

        let stdin:  In.fd  = stdin
        let stdout: Out.fd = stdout
        let stderr: Out.fd = stderr
      end


    module Repl =
      struct
        let prompt = prompt
      end

(*
    let getc_in: char option t =
      getc stdin

    let get_line_in: string option t =
      get_line stdin
 *)


    module Stdout =
      struct
        open File
        let putc (c:char): unit t =
          Out.putc c stdout

        let string (s:string): unit t =
          Out.string s stdout

        let line (s:string): unit t =
          Out.line s stdout

        let newline: unit t =
          Out.newline stdout

        let fill n c = Out.fill n c stdout
      end


    module Stderr =
      struct
        open File
        let putc (c:char): unit t =
          Out.putc c stderr

        let string (s:string): unit t =
          Out.string s stderr

        let line (s:string): unit t =
          Out.line s stderr

        let newline: unit t =
          Out.newline stderr

        let fill n c = Out.fill n c stderr
      end
  end


module Output (Io:SIG) =
  struct
    type fd = Io.File.Out.fd

    type t =
      | Leaf of (fd -> unit Io.t)
      | Plus of t * t


    let empty: t =
      Leaf (fun _ -> Io.return ())

    let (<+>) (p1:t) (p2:t): t =
      Plus (p1,p2)

    let char c = Leaf (Io.File.Out.putc c)

    let substring str start len = Leaf (Io.File.Out.substring str start len)

    let string str = Leaf (Io.File.Out.string str)

    let line str = Leaf (Io.File.Out.line str)

    let newline = Leaf Io.File.Out.newline

    let fill n c = Leaf (Io.File.Out.fill n c)

    let run (fd:fd) (m:t): unit Io.t =
      let rec run = function
        | Leaf f ->
           f fd
        | Plus (p1, p2) ->
           Io.(run p1 >>= fun _ -> run p2)
      in
      run m
  end
