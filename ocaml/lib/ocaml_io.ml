open Common



module Buffer:
sig
  type t
  val make: int ->
            (Bytes.t -> int -> int -> int) ->
            (Bytes.t -> int -> int -> int) ->
            t
  val size: t -> int
  val reset: t -> unit
  val content: t -> string
  val is_ok: t -> bool
  val is_empty: t -> bool
  val is_full: t -> bool
  val flush: t -> unit
  val getc: t -> char option
  val putc: t -> char -> unit
  val put_string: t -> string -> unit
end =
  struct
    type t = {
        mutable rp: int; (* The content of the buffer is between the read and
                            the write pointer. *)
        mutable wp: int;
        mutable flag: bool; (* ok flag *)
        read:  Bytes.t -> int -> int -> int; (* refill function *)
        write: Bytes.t -> int -> int -> int; (* flush function *)
        bytes: Bytes.t}

    let size (b:t): int =
      Bytes.length b.bytes

    let make (n:int)
          (read:Bytes.t -> int -> int -> int)
          (write:Bytes.t -> int -> int -> int)
        : t =
      assert (n > 0);
      assert (n <= Sys.max_string_length);
      {rp = 0; wp = 0; bytes = Bytes.create n; flag = true; read; write}

    let is_ok (b:t): bool =
      b.flag

    let is_empty (b:t): bool =
      b.rp = b.wp

    let reset (b:t): unit =
      b.rp <- 0;
      b.wp <- 0

    let content (b:t): string =
      Bytes.sub_string b.bytes b.rp (b.wp - b.rp)

    let is_full (b:t): bool =
      b.wp = Bytes.length b.bytes

    let fill (b:t): unit =
      assert (is_empty b);
      assert (is_ok b);
      let n = b.read b.bytes 0 (Bytes.length b.bytes) in
      b.rp <- 0; b.wp <- n;
      if n = 0 then
        b.flag <- false

    let flush (b:t): unit =
      if not (is_empty b) && is_ok b then
        let n = b.write b.bytes b.rp (b.wp - b.rp) in
        if n = 0 then
          b.flag <- false
        else
          reset b

    let getc (b:t): char option =
      if is_empty b then
        fill b;
      if is_empty b then
        None
      else
        (let c = Bytes.get b.bytes b.rp in
         b.rp <- b.rp + 1;
         Some c)

    let putc (b:t) (c:char): unit =
      if is_full b then
        flush b;
      assert (not (is_full b));
      Bytes.set b.bytes b.wp c;
      b.wp <- b.wp + 1

    let put_string (b:t) (s:string): unit =
      for i = 0 to String.length s - 1 do
        putc b s.[i]
      done
  end






module File_system:
sig
  type t
  val make: unit -> t
  val flush_all: t -> unit
  val get_line: t -> string option
  val put_string: t -> string -> unit
  val put_line: t -> string -> unit
  val put_newline: t -> unit
  val put_stderr_string: t -> string -> unit
  val put_stderr_line: t -> string -> unit
  val put_stderr_newline: t -> unit

  type in_file
  type out_file
  val stdin: in_file
  val stdout: out_file
  val stderr: out_file
  val getc: t -> in_file -> char option
  val putc: t -> out_file -> char -> unit
  val open_for_read: t -> string -> in_file option
  val open_for_write: t -> string -> out_file option
  val create_file: t -> string -> out_file option
  val close_in_file:   t -> in_file -> unit
  val close_out_file:  t -> out_file -> unit
  val flush: t -> out_file -> unit
end
  =
  struct
    type file =
      | Read of Unix.file_descr * Buffer.t
      | Write of Unix.file_descr * Buffer.t
      | Free of int

    type t = {mutable files: file array;
              mutable first_free: int;
              line_buf: Buffer.t}

    type in_file = int
    type out_file = int

    let buffer_size = 4096

    let unix_read (fd:Unix.file_descr) (b:Bytes.t) (ofs:int) (n:int): int =
      try
        Unix.read fd b ofs n
      with Unix.Unix_error _ ->
        0

    let unix_write (fd:Unix.file_descr) (b:Bytes.t) (ofs:int) (n:int): int =
      try
        Unix.write fd b ofs n
      with Unix.Unix_error _ ->
        0

    let readable_file (fd:Unix.file_descr): file =
      Read (fd, Buffer.make
                  buffer_size
                  (unix_read fd)
                  (fun _ _ _ -> assert false))

    let writable_file (fd:Unix.file_descr): file =
      Write (fd, Buffer.make
                   buffer_size
                   (fun _ _ _ -> assert false)
                   (unix_write fd))

    let make (): t =
      {first_free = -1;
       files =
         [| readable_file Unix.stdin;
            writable_file Unix.stdout;
            writable_file Unix.stderr |];
       line_buf =
         let fr _ _ _ = assert false in
         let fw _ _ _ = assert false in
         Buffer.make 200 fr fw
      }


    let put_to_files (fs:t) (file:file): int option =
      if fs.first_free >= 2 then
        begin
          let fd = fs.first_free in
          match fs.files.(fd) with
          | Free n ->
             fs.first_free <- n;
             fs.files.(fd) <- file;
             Some fd
          | _ ->
             assert false (* Cannot happen, must be free! *)
        end
      else
        begin
          let nfiles = Array.length fs.files in
          let files = Array.make (nfiles + 1) file in
          Array.blit fs.files 0 files 0 nfiles;
          fs.files <- files;
          Some nfiles
        end

    let writable_buffer (fs:t) (fd:int): Buffer.t =
      assert (fd < Array.length fs.files);
      match fs.files.(fd) with
      | Write (_,b) ->
         b
      | _ ->
         assert false

    let readable_buffer (fs:t) (fd:int): Buffer.t =
      assert (fd < Array.length fs.files);
      match fs.files.(fd) with
      | Read (_,b) ->
         b
      | _ ->
         assert false


    let getc (fs:t) (fd:in_file): char option =
      Buffer.getc (readable_buffer fs fd)

    let putc (fs:t) (fd:out_file) (c:char): unit =
      Buffer.putc (writable_buffer fs fd) c


    let open_for_read (fs:t) (path:string): in_file option =
      try
        put_to_files
          fs
          (readable_file (Unix.openfile path [Unix.O_RDONLY] 0o640))
      with Unix.Unix_error _ ->
        None

    let open_for_write (fs:t) (path:string): out_file option =
      try
        put_to_files
          fs
          (writable_file (Unix.openfile path [Unix.O_WRONLY] 0o640))
      with Unix.Unix_error _ ->
        None

    let create_file (fs:t) (path:string): out_file option =
      try
        put_to_files
          fs
          (writable_file (Unix.openfile path [Unix.O_CREAT] 0o640))
      with Unix.Unix_error _ ->
        None

    let unix_file_descriptor (fs:t) (fd:int): Unix.file_descr =
      assert (fd < Array.length fs.files);
      match fs.files.(fd) with
      | Read (fd,b) -> fd
      | Write (fd,b) -> fd
      | Free _ ->
         assert false


    let close_file (fs:t) (fd:int): unit =
      assert (fd < Array.length fs.files);
      match fs.files.(fd) with
      | Read (fd,b) ->
         Unix.close fd
      | Write (fd,b) ->
         Buffer.flush b;
         Unix.close fd
      | Free _ ->
         ()

    let close_in_file (fs:t) (fd:in_file): unit =
      close_file fs fd

    let close_out_file (fs:t) (fd:out_file): unit =
      close_file fs fd


    let flush (fs:t) (fd:out_file) : unit =
      assert (fd < Array.length fs.files);
      match fs.files.(fd) with
      | Write (_,b) ->
         Buffer.flush b
      | _ ->
           ()

    let flush_all (fs:t): unit =
      for i = 0 to Array.length fs.files - 1 do
        flush fs i
      done

    let stdin: in_file = 0

    let stdout: out_file = 1

    let stderr: out_file = 2

    let stdin_buffer (fs:t): Buffer.t =
      readable_buffer fs stdin


    let stdout_buffer (fs:t): Buffer.t =
      writable_buffer fs stdout


    let stderr_buffer (fs:t): Buffer.t =
      writable_buffer fs stderr


    let get_line_file (fs:t) (fd:in_file): string option =
      assert (fd < Array.length fs.files);
      let b = readable_buffer fs fd in
      Buffer.reset fs.line_buf;
      let content () = Some (Buffer.content fs.line_buf) in
      let len = Buffer.size fs.line_buf
      in
      let rec read (i:int): string option =
        if i = len then
          content ()
        else
          begin
            match Buffer.getc b with
            | None ->
               if i = 0 then
                 None
               else
                 content ()
            | Some c ->
               if c = '\n' then
                 content ()
               else
                 begin
                   Buffer.putc fs.line_buf c;
                   read (i+1)
                 end
          end
      in
      read 0

    let get_line (fs:t): string option =
      Buffer.flush (stdout_buffer fs);
      get_line_file fs 0

    let put_string (fs:t) (s:string): unit =
      Buffer.put_string (stdout_buffer fs) s

    let put_line (fs:t) (s:string): unit =
      let b = stdout_buffer fs in
      Buffer.put_string b s;
      Buffer.putc b '\n'

    let put_newline (fs:t): unit =
      let b = stdout_buffer fs in
      Buffer.putc b '\n'

    let put_stderr_string (fs:t) (s:string): unit =
      Buffer.put_string (stderr_buffer fs) s

    let put_stderr_line (fs:t) (s:string): unit =
      let b = stderr_buffer fs in
      Buffer.put_string b s;
      Buffer.putc b '\n'

    let put_stderr_newline (fs:t): unit =
      Buffer.putc (stderr_buffer fs) '\n'
  end (* File_system *)











module type IO_TYPE =
  sig
    include Monad.MONAD
    val exit: int -> 'a t
    val execute: unit t -> unit
    val command_line: string array t
    val get_line:    string option t
    val put_string:  string -> unit t
    val put_line:    string -> unit t
    val put_newline: unit t
    val put_stderr_string:  string -> unit t
    val put_stderr_line:    string -> unit t
    val put_stderr_newline: unit t

    type in_file
    type out_file
    val stdin:  in_file
    val stdout: out_file
    val stderr: out_file
    val getc: in_file -> char option t
    val putc: out_file -> char -> unit t
    val open_for_read:  string -> in_file option t
    val open_for_write: string -> out_file option t
    val create_file:    string -> out_file option t
    val close_in_file:  in_file -> unit t
    val close_out_file: out_file -> unit t
    val flush: out_file -> unit t
  end


module IO: IO_TYPE =
  struct
    include
      Monad.Make(
          struct
            type 'a t = File_system.t -> ('a,int) result * File_system.t
            let make (a:'a): 'a t =
              fun fs -> Ok a, fs
            let bind (m:'a t) (f:'a -> 'b t): 'b t =
              (fun fs ->
                let r,fs = m fs in
                match r with
                | Ok a ->
                   f a fs
                | Error code ->
                   Error code, fs
              )
          end)

    type in_file = File_system.in_file
    type out_file = File_system.out_file

    let exit (code:int): 'a t =
      fun fs -> Error code, fs

    let execute (p:unit t): unit =
      let r,fs = p (File_system.make ()) in
      File_system.flush_all fs;
      Pervasives.exit
        (match r with
         | Ok _ ->
            0
         | Error c ->
            c)

    let command_line: string array t =
      fun fs -> Ok Sys.argv, fs

    let get_line: string Option.t t =
      fun fs ->
      Ok (File_system.get_line fs), fs

    let put_string (str:string): unit t =
      fun fs -> Ok (File_system.put_string fs str),fs

    let put_newline: unit t =
      fun fs -> Ok (File_system.put_newline fs),fs

    let put_line (str:string): unit t =
      fun fs -> Ok (File_system.put_line fs str),fs

    let put_stderr_string (str:string): unit t =
      fun fs -> Ok (File_system.put_stderr_string fs str), fs

    let put_stderr_newline: unit t =
      fun fs -> Ok (File_system.put_stderr_newline fs), fs

    let put_stderr_line (str:string): unit t =
      fun fs -> Ok (File_system.put_stderr_line fs str), fs

    let getc (fd:in_file): char option t =
      fun fs -> Ok (File_system.getc fs fd), fs

    let putc (fd:out_file) (c:char): unit t =
      fun fs -> Ok (File_system.putc fs fd c), fs

    let stdin:  in_file = File_system.stdin
    let stdout: out_file = File_system.stdout
    let stderr: out_file = File_system.stderr

    let open_for_read (path:string): in_file option t =
      fun fs -> Ok (File_system.open_for_read fs path), fs

    let open_for_write (path:string): out_file option t =
      fun fs -> Ok (File_system.open_for_write fs path), fs

    let create_file (path:string): out_file option t =
      fun fs -> Ok (File_system.create_file fs path), fs

    let close_in_file (fd:in_file): unit t =
      fun fs -> Ok (File_system.close_in_file fs fd), fs

    let close_out_file (fd:out_file): unit t =
      fun fs -> Ok (File_system.close_out_file fs fd), fs

    let flush (fd:out_file): unit t =
      fun fs -> Ok (File_system.flush fs fd), fs
  end (* IO *)
