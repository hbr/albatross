open Common_module_types
open Common


module type PATH =
  sig
    val separator: char
    val delimiter: char
    val basename: string -> string
    val dirname: string -> string
    val extname: string -> string
  end


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







module type READABLE =
  sig
    type t
    val has_more: t -> bool
    val peek: t -> char
    val advance: t -> t
  end





module type WRITABLE =
  sig
    type t
    val needs_more: t -> bool
    val putc: t -> char ->  t
    val putend: t -> t
  end


module type FILTER =
  sig
    module Readable: READABLE
    type t
    val needs_more: t -> bool
    val putc: t -> char -> t * Readable.t
    val put_end: t -> t * Readable.t
  end





module type SCANNER =
  sig
    type t
    val can_receive: t -> bool
    val receive: char -> t -> t
    val end_buffer: t -> t
    val end_stream: t -> t
  end


module type S0 =
  sig
    type in_file
    type out_file

    val stdin:  in_file
    val stdout: out_file
    val stderr: out_file

    include MONAD

    val exit: int -> 'a t
    val execute: unit t -> unit

    val command_line: string array t

    val open_for_read:  string -> in_file  option t
    val open_for_write: string -> out_file option t
    val create: string -> out_file option t
    val close_in:  in_file  -> unit t
    val close_out: out_file -> unit t
    val flush: out_file -> unit t
    val flush_all: unit t

    val getc: in_file -> char option t
    val putc: char -> out_file  ->  unit t
    val get_line: in_file -> string option t
    val scan: (char,'a) Scan.t -> in_file -> 'a t
    val put_substring: string -> int -> int -> out_file -> unit t

    module Scan: functor (S:SCANNER) ->
                 sig
                   val buffer: in_file -> S.t -> S.t t
                   val stream: in_file -> S.t -> S.t t
                 end
  end


module type S =
  sig
    include S0

    val read_file:   string -> 'a t -> (in_file  -> 'a t) -> 'a t
    val write_file:  string -> 'a t -> (out_file -> 'a t) -> 'a t
    val create_file: string -> 'a t -> (out_file -> 'a t) -> 'a t

    val put_string: string -> out_file -> unit t
    val put_line:   string -> out_file -> unit t
    val put_newline:   out_file -> unit t
    val fill: char -> int -> out_file -> unit t

    val getc_in: char option t
    val get_line_in: string option t

    val putc_out: char -> unit t
    val put_string_out: string -> unit t
    val put_line_out: string -> unit t
    val put_newline_out: unit t

    val putc_err: char -> unit t
    val put_string_err: string -> unit t
    val put_line_err: string -> unit t
    val put_newline_err: unit t
  end


module String_reader =
  struct
    type t = {s: string; pos:int; beyond:int}

    let of_substring (s:string) (start:int) (len:int): t =
      assert (0 <= start);
      assert (start + len <= String.length s);
      {s; pos = start; beyond = start + len}

    let of_string (s:string): t =
      of_substring s 0 (String.length s)

    let has_more (r:t): bool =
      r.pos < r.beyond

    let peek (r:t): char =
      assert (has_more r);
      r.s.[r.pos]

    let advance (r:t): t =
      assert (has_more r);
      {r with pos = r.pos + 1}
  end

module Fill_reader =
  struct
    type t = {n:int; c:char}
    let has_more (r:t): bool =
      r.n > 0
    let peek (r:t): char =
      r.c
    let advance (r:t): t =
      {r with n = r.n - 1}
    let make (n:int) (c:char): t =
      {n;c}
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





module Make (M:S0): S =
  struct
    include M

    let read_file
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

    let put_string (s:string) (fd:out_file): unit t =
      put_substring s 0 (String.length s) fd

    let put_newline (fd:out_file): unit t =
      putc '\n' fd

    let put_line (s:string) (fd:out_file): unit t =
      put_string s fd >>= fun _ ->
      put_newline fd


    let fill (c:char) (n:int) (fd:out_file): unit t =
      let rec put i =
        if i = n then
          return ()
        else
          putc c fd >>= fun _ -> put (i+1)
      in
      put 0


    let getc_in: char option t =
      getc stdin

    let get_line_in: string option t =
      get_line stdin

    let putc_out (c:char): unit t =
      putc c stdout

    let put_string_out (s:string): unit t =
      put_string s stdout

    let put_line_out (s:string): unit t =
      put_line s stdout

    let put_newline_out: unit t =
      put_newline stdout

    let putc_err (c:char): unit t =
      putc c stderr

    let put_string_err (s:string): unit t =
      put_string s stderr

    let put_line_err (s:string): unit t =
      put_line s stderr

    let put_newline_err: unit t =
      put_newline stderr
  end


module Output (Io:S) =
  struct
    type out_file = Io.out_file

    include
      Monad.Of_sig_min (
          struct
            type 'a t = out_file -> 'a Io.t
            let return (a:'a) (_:out_file): 'a Io.t =
              Io.return a
            let (>>=) (m:'a t) (f:'a -> 'b t) (fd:out_file): 'b Io.t =
              Io.(m fd >>= fun a -> f a fd)
          end
        )

    let putc = Io.putc
    let put_substring = Io.put_substring
    let put_string = Io.put_string
    let put_line = Io.put_line
    let put_newline = Io.put_newline

    let fill = Io.fill

    let run (fd:out_file) (m:'a t): 'a Io.t =
      m fd
 end
