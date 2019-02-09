open Common_module_types



(* Library modules *)
let _ =
  Document.test ();
  Pretty_printer.test ();
  Character_parser.test ()



(* Albatross modules *)
let _ =
  Term_printer.test();
  Type_checker.test()





(* Draft version of an output module with indentation *)
module Output_indent (IO:Io.S):
sig
  include Monad.OUTPUT_INDENT
  val eval: int -> int -> IO.out_file -> 'a t -> 'a IO.t
end
  =
  struct
    module State =
      struct
        type t = {indent: int; column: int; fd:IO.out_file}

        let make indent column fd=
          {indent; column; fd}

        let indent (s:t): int =
          s.indent

        let column (s:t): int =
          s.column

        let file_descriptor (s:t): IO.out_file =
          s.fd

        let increment (i:int) (s:t): t =
          {s with indent = s.indent + i}

        let decrement (i:int) (s:t): t =
          assert (i <= s.indent);
          {s with indent = s.indent - i}

        let newline (s:t): t =
          {s with column = 0}

        let write (n:int) (s:t): t =
          {s with column = s.column + n}
      end

    include Monad.State_into (IO) (State)

    let indent (i:int) (m:'a t): 'a t =
      update (State.increment i) >>= fun _ ->
      m >>= fun a ->
      update (State.decrement i) >>= fun _ ->
      make a

    let write_something
          (len:int)
          (write: IO.out_file -> unit IO.t) : 'a t =
      get >>= fun state ->
      let fd = State.file_descriptor state in
      let nfill =
        let column = State.column state
        and indent = State.indent state in
        if column < indent then
          indent - column
        else
          0
      in
      (if nfill = 0 then
         write fd
       else
         IO.(fill fd ' ' nfill >>= fun _ -> write fd))
      |> lift >>= fun _ ->
      put (State.write (nfill + len) state)

    let fill (c:char) (i:int): unit t =
      write_something i (fun fd -> IO.fill fd c i)

    let putc (c:char): unit t =
      write_something 1 (fun fd -> IO.putc fd c)

    let put_substring (i:int) (len:int) (s:string): unit t =
      assert (i <= len);
      write_something len (fun fd -> IO.put_substring fd i len s)

    let put_string (s:string): unit t =
      put_substring 0 (String.length s) s

    let put_newline: unit t =
      get >>= fun state ->
      IO.(putc (State.file_descriptor state) '\n') |> lift >>= fun _ ->
      put (State.newline state)

    let put_line (s:string): unit t =
      put_string s >>= fun _ -> put_newline


    let eval (indent:int) (column:int) (fd:IO.out_file) (m:'a t): 'a IO.t =
      eval (State.make indent column fd) m
  end



module Out = Output_indent (Ocaml_io.IO)
(*
let _ =
  let open Ocaml_io in
  let test =
    Out.(put_line "Hello" >>= fun _ ->
         put_line "world!">>= fun _ ->
         indent
           2
           (put_line "1" >>= fun _ ->
            (indent
               2
               (put_line "1.1" >>= fun _ ->
                put_newline >>= fun _ ->
                put_string "more..." >>= fun _ ->
                fill ' ' 5 >>= fun _ ->
                put_string "after 5 blanks" >>= fun _ ->
                putc '|' >>= fun _ ->
                put_newline)
            )
            >>= fun _ ->
            put_line "2" >>= fun _ -> put_line "more of 2")
    )
  in
  IO.(Out.(eval 0 0 stdout test) |> execute)
 *)
