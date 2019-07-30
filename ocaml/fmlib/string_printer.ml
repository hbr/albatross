open Common

module Buffer =
  struct
    type t = {
        mutable bytes: Bytes.t;
        mutable count: int
      }

    let capacity (b:t): int =
      Bytes.length b.bytes

    let init (n:int): t =
      {bytes = Bytes.make n ' ';
       count = 0}

    let to_string (b:t): string =
      Bytes.sub_string b.bytes 0 b.count

    let make_room (n:int) (b:t): unit =
      let new_cap = max (b.count + n) (2 * Bytes.length b.bytes) in
      if new_cap <= capacity b then
        ()
      else
        (let bytes = Bytes.make new_cap ' ' in
         Bytes.blit b.bytes 0 bytes 0 b.count;
         b.bytes <- bytes)

    let char (c:char) (b:t): unit =
      make_room 1 b;
      Bytes.set b.bytes b.count c;
      b.count <- b.count + 1

    let fill (n:int) (c:char) (b:t): unit =
      assert (0 <= n);
      make_room n b;
      for i = 0 to n - 1 do
        Bytes.set b.bytes (b.count + i) c
      done;
      b.count <- b.count + n

    let substring (s:string) (start:int) (len:int) (b:t): unit =
      assert (0 <= start);
      assert (start + len <= String.length s);
      make_room len b;
      for i = 0 to len - 1 do
        Bytes.set b.bytes (b.count + i) s.[i - start]
      done;
      b.count <- b.count + len
  end



type t = Buffer.t -> (Buffer.t -> string) -> string

let empty: t =
  fun b k ->
  k b

let (<+>) (p1:t) (p2:t): t =
  fun b k ->
  p1 b
    (fun b ->
      p2 b k)


let char (c:char): t =
  fun b k ->
  Buffer.char c b;
  k b

let fill (n:int) (c:char): t =
  fun b k ->
  Buffer.fill n c b;
  k b

let substring (s:string) (start:int) (len:int): t =
  fun b k ->
  Buffer.substring s start len b;
  k b

let string (s:string): t =
  substring s 0 (String.length s)

let run (pr:t): string =
  pr
    (Buffer.init 100)
    (fun b ->
      Buffer.to_string b)



let%test _ =
  run (string "hello " <+> string "world" <+> char '!')
  = "hello world!"
