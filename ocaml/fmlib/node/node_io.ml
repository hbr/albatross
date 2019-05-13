open Fmlib
open Common
open Common_module_types

(* IO Interface *)
module type IO =
  sig
    include MONAD

    type in_file
    type out_file
    type in_stream
    type out_stream

    val exit: int -> 'a t
    val execute: unit t -> unit


    module Reader (P:Io.WRITABLE):
    sig
      val parse_file: string -> P.t -> P.t option t
    end

    module Filter (F:Io.FILTER):
    sig
      type error =
        | Cannot_open_input
        | Cannot_open_output
        | Cannot_write of F.t * F.Readable.t

      val parse_file: string -> string -> F.t -> (F.t, error) result t
    end
  end





module World = Io.Buffers (Io_buffer)

module M =
  struct
    type 'a t = World.t -> ('a -> unit) -> unit

    let return (a:'a) (_:World.t) (k:'a -> unit): unit =
      k a

    let (>>=) (m:'a t) (f:'a -> 'b t) (w:World.t) (k:'b -> unit): unit =
      m w
        (fun a ->
          f a w k)
  end

include Monad.Of_sig_min (M)

let write1 (fd:int) (buf:Io_buffer.t) (_:World.t) (k:int -> unit): unit =
  File_system.write fd buf k

let flush (fd:int) (buf:Io_buffer.t) (w:World.t) (k:unit option->unit): unit =
  let rec wrt () =
    if Io_buffer.is_empty buf then
      return @@ Some ()
    else
      write1 fd buf >>= fun n ->
      if n = 0 then
        return None
      else
        wrt ()
  in
  wrt () w k


let write (i:int) (w:World.t) (k:unit option -> unit): unit =
  assert (World.is_open_write w i);
  let fd,buf = World.writable_file w i in
  flush fd buf w k

let read (i:int) (w:World.t) (k:int -> unit): unit =
  assert (World.is_open_read w i);
  let fd,buf = World.readable_file w i in
  assert (not (Io_buffer.is_full buf));
  File_system.read fd buf k

let flush_all (w:World.t) (k: unit -> unit): unit =
  let rec flush i =
    let j = World.find_open w i in
    if j = World.capacity w then
      return ()
    else
      (if World.is_open_write w j then
         write j
       else
         return @@ Some ())
      >>= fun _ ->
      flush (j+1)
  in
  flush 0 w k

let exit (code:int) (w:World.t) (k:'a -> unit): unit =
  (flush_all >>= fun _ -> Process.exit code) w k

type in_file  = int
type out_file = int

let stdin:  in_file  = 0
let stdout: out_file = 1
let stderr: out_file = 2

let buffer_size = 4096 (* 16K: 16384, 32K: 32768, 64K: 65536, 2000 loc ~ 56K,
                          3000 loc ~ 85K *)


let execute (program:unit t): unit =
  let w = World.make buffer_size in
  let i0 = World.occupy_readable w stdin in
  assert (i0 = stdin);
  let i1 = World.occupy_writable w stdout in
  assert (i1 = stdout);
  let i2 = World.occupy_writable w stderr in
  assert (i2 = stderr);
  (program >>= fun _ -> flush_all) w identity

let create_directory (path:string) (_:World.t) (k:unit option -> unit): unit =
  File_system.mkdir path k

let remove_directory (path:string) (_:World.t) (k:unit option -> unit): unit =
  File_system.rmdir path k


let open_for_read (path:string) (w:World.t) (k:in_file option -> unit): unit =
  File_system.open_ path "r"
    (function
     | None ->
        k None
     | Some fd ->
        k @@ Some (World.occupy_readable w fd))

let open_for_write (path:string) (w:World.t) (k:out_file option -> unit): unit =
  File_system.open_ path "w"
    (function
     | None ->
        k None
     | Some fd ->
        k @@ Some (World.occupy_writable w fd))

let close (i:int) (w:World.t) (k:unit option -> unit): unit =
  if World.is_open_read w i then
    let fd,_ = World.readable_file w i in
    World.release w i;
    File_system.close fd k
  else if World.is_open_write w i then
    let fd,buf = World.readable_file w i in
    World.release w i;
    (flush fd buf w
       (fun _ -> File_system.close fd k))
  else
    assert false (* Illegal call: File not open! *)

let close_readable (fd:in_file) (w:World.t) (k:unit option -> unit): unit =
  close fd w k

let close_writable (fd:in_file) (w:World.t) (k:unit option -> unit): unit =
  close fd w k

let getc (i:in_file) (w:World.t) (k:char option -> unit): unit =
  let _,buf = World.readable_file w i in
  let o = Io_buffer.getc buf in
  (match o with
   | None ->
      (read i >>= fun _ ->
       return @@ Io_buffer.getc buf)
   | Some c ->
      return @@ Some c
  ) w k


let putc (i:out_file) (c:char) (w:World.t) (k:unit option -> unit): unit =
  let fd,buf = World.writable_file w i in
  let o = Io_buffer.putc buf c in
  (match o with
   | None ->
      (flush fd buf >>= fun _ ->
       return @@ Io_buffer.putc buf c)
   | Some () ->
      return @@ Some ()
  ) w k

let getchar = getc stdin
let putchar = putc stdout
let errchar = putc stderr
