module Ocaml_char = Char
module Ocaml_string = String
module Ocaml_list = List


module Void:
sig
  type t
end =
  struct
    type t = int
  end


module Unit:
sig
  type t = unit
end =
  struct
    type t = unit
  end


module Int:
sig
  type t = int
end =
  struct
    type t = int
  end



module Float:
sig
  type t = float
end =
  struct
    type t = float
  end



module Either =
  struct
    type ('a,'b) t =
      | Left of 'a
      | Right of 'b
    let left a = Left a
    let right b = Right b
  end

module type FUNCTOR =
  sig
    type _ t
    val map: ('a -> 'b) -> 'a t -> 'b t
  end



module Char =
  struct
    include Char
    let is_lower (c:char): bool =
      'a' <= c && c <= 'z'
    let is_upper (c:char): bool =
      'A' <= c && c <= 'Z'
    let is_letter (c:char): bool =
      is_lower c || is_upper c
    let is_digit (c:char): bool =
      '0' <= c && c <= '9'
  end



module String =
  struct
    include String

    let one (c:char): string =
      String.make 1 c

    let find (f:char -> bool) (start:int) (s:string): int =
      let len = String.length s in
      let rec find i =
        if i = len || f s.[i] then
          i
        else
          find (i+1)
      in
      find start

    let list (s:string): char list =
      let rec list cs i =
        if i = 0 then
          cs
        else
          let j = i - 1 in
          list (s.[j]::cs) j
      in
      list [] (length s)

    let of_list (cs:char list): string =
      let rec str cs i =
        match cs with
        | [] ->
           Bytes.create i
        | c::cs ->
           let bs = str cs (i+1) in
         Bytes.set bs i c;
         bs
      in
      let bs = str cs 0 in
      Bytes.unsafe_to_string bs
  end






module List =
  struct
    include List
    include
      Monad.Make (
          struct
            type 'a t = 'a list
            let make (a:'a): 'a t =
              [a]
            let rec bind (m:'a t) (f:'a -> 'b t): 'b t =
              match m with
              | [] ->
                 []
              | hd :: tl ->
                 f hd @ bind tl f
          end
        )
    let find (f:'a -> bool) (l:'a t): 'a option =
      try
        Some (List.find f l)
      with Not_found ->
        None

    module Monadic (M:Monad.MONAD) =
      struct
        let foldi_left (f:int -> 'a -> 'b -> 'b M.t) (l:'a t) (b:'b)
                : 'b M.t =
          let rec foldi i l b =
            match l with
            | [] ->
               M.make b
            | hd :: tl ->
               M.(f i hd b >>= foldi (i+1) tl)
          in
          foldi 0 l b

        let fold_left (f:'a -> 'b -> 'b M.t) (l:'a t) (b:'b): 'b M.t =
          foldi_left (fun _ -> f) l b

        let fold_right (f:'a -> 'b -> 'b M.t) (l:'a t) (b:'b): 'b M.t =
          fold_left f (rev l) b
      end
  end







module type SEXP =
  sig
    type t =
      | Atom of string
      | Seq of t array
    val string: t -> string
  end




module Sexp =
  struct
    type t =
      | Atom of string
      | Seq of t array
    let string(s:t): string =
      let rec string0 i s =
        match s with
        | Atom str ->
           str
        | Seq arr ->
           let s0 =
             String.concat
               ""
               (List.map (string0 (i+1)) (Array.to_list arr))
           in
           if i = 0 then
             s0
           else
             "(" ^ s0 ^ ")"
      in
      string0 0 s
  end



module Scan =
  struct
    type ('token,'a) result =
      | More of ('token,'a) t
      | End of 'a
    and ('token,'a) t = 'token option -> ('token,'a) result
  end
