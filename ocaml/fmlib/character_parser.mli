open Common
open Common_module_types


(** Position within a stream.*)
module Position:
sig
  type t
  val line:   t -> int
  val column: t -> int
  val next_line:   t -> t
  val next_column: t -> t
end

module Located:
sig
  type 'a t
  val make: Position.t -> 'a -> Position.t -> 'a t
  val map: ('a -> 'b) -> 'a t -> 'b t
  val use: 'a t -> (Position.t -> 'a -> Position.t -> 'b) -> 'b
  val start: 'a t -> Position.t
  val end_:  'a t -> Position.t
  val range: 'a t -> Position.t * Position.t
  val value: 'a t -> 'a
end

module type CONTEXT =
  sig
    type t
    type msg
    val message: t -> msg
    val position: t -> Position.t
    val line: t -> int
    val column: t -> int
  end


module type DEAD_END =
  sig
    type t
    type msg
    type context
    val message: t -> msg
    val position: t -> Position.t
    val line: t -> int
    val column: t -> int
    val offside: t -> (int * int option) option
    val contexts: t -> context list
  end





module type PARSER =
  sig
    (** Parser Type *)
    type parser

    (** Does the parser need more tokens (i.e. either [put_char] or [put_end])?
     *)
    val needs_more: parser -> bool

    (** Has the parser terminated (opposite of [needs_more p])? *)
    val has_ended:  parser -> bool

    (** The current position. *)
    val position:   parser -> Position.t

    (** The current line. *)
    val line:   parser -> int

    (** The current column. *)
    val column: parser -> int

    (** [put_char p c] feeds the parser [p] with the character token [c]. Only
        possible if [needs_more p] is valid. *)
    val put_char: parser -> char -> parser

    (** [put_end p] signals to the parser [p] the end of stream. Only possible
     if          [needs_more p] is valid.*)
    val put_end: parser -> parser
  end





(** Simple Parser. *)
module Simple (Final:ANY):
sig
  (** {1 Modules and Types} *)

  module Context: CONTEXT with type msg = string
  module Dead_end: DEAD_END with type msg = string
                             and type context = Context.t

  type final = Final.t
  type token = char option


  (** {1 Combinators} *)


  (** {2 Basic Combinators} *)

  include Generic_parser.BASIC
  val fail: string -> 'a t
  val backtrackable: 'a t -> string -> 'a t

  (** {2 More Combinators} *)

  include Parse_combinators.COMBINATORS with type 'a tp = 'a t

  (** {2 Character Combinators} *)

  val expect: (char -> bool) -> string -> char t
  val expect_end: unit t
  val whitespace_char: char t
  val whitespace: int t
  val one_of_chars: string -> string -> unit t
  val string: string -> unit t
  val char: char -> unit t
  val space: unit t
  val letter: char t
  val digit:  char t
  val word: (char->bool) -> (char->bool) -> string -> string t
  val variable: (char->bool) -> (char->bool) -> String_set.t
                -> string -> string t


  (** {2 Position Combinator} *)

  val get_position: (Position.t) t
  val located: 'a t -> 'a Located.t t


  (** {2 Indentation Combinators} *)

  val absolute: 'a t -> 'a t
  (** [absolute p] is the parser [p] whose set of possible indentation
     positions is the singleton set consisting of the indentation position of
     the first token.. *)

  val indented: bool -> 'a t -> 'a t
  val detached: 'a t -> 'a t
  val get_bounds: (int * int option) t

  val one_or_more_aligned:  'a t -> 'a list t
  val zero_or_more_aligned: 'a t -> 'a list t
  val skip_one_or_more_aligned:  'a t -> int t
  val skip_zero_or_more_aligned: 'a t -> int t


  (** {2 Context Combinator} *)

  val in_context: string -> 'a t -> 'a t


  (** {1 Parser} *)

  (** {2 During Parsing} *)

  include PARSER


  (** {2 Terminated Parser} *)

  (** The result the parser has produced which is either a final value or a
     list of dead ends. Only valid if the parser has terminated. *)
  val result: parser -> (final,error list) result

  val result_string: parser -> (final -> string) -> string

  (** The list of tokens (i.e. optional characters) which the parser has not
     processed at the point of termination. *)
  val lookahead: parser -> token list

  val lookahead_string: parser -> string


  (** {2 Create and Run the Parser} *)

  (** [make pc] makes a parser from a parser combinator [pc].*)
  val make: final t -> parser

  (** [run p str] makes a parser from the combinator [pc] and runs the parser
     on the string [str]. *)
  val run: final t -> string -> parser
end




(** Advanced Parser. *)
module Advanced (State:ANY) (Final:ANY) (Problem:ANY) (Context_msg:ANY):
sig
  (** {1 Modules and Types} *)

  module Context:  CONTEXT with type msg = Context_msg.t
  module Dead_end: DEAD_END with type msg = Problem.t
                             and type context = Context.t

  type final = Final.t
  type token = char option


  (** {1 Combinators} *)


  (** {2 Basic Combinators} *)

  include Generic_parser.BASIC with type error = Dead_end.t
  val fail: Problem.t -> 'a t
  val backtrackable: 'a t -> Problem.t -> 'a t

  (** {2 More Combinators} *)

  include Parse_combinators.COMBINATORS with type 'a tp = 'a t

  (** {2 Character Combinators} *)

  val expect: (char -> bool) -> Problem.t -> char t
  val expect_end:  Problem.t -> unit t
  val whitespace_char: Problem.t -> char t
  val whitespace: Problem.t -> int t
  val one_of_chars: string -> Problem.t -> unit t
  val string: string -> (int -> Problem.t) -> unit t
  val char: char -> Problem.t -> unit t
  val space: Problem.t -> unit t
  val letter: Problem.t -> char t
  val digit:  Problem.t -> char t
  val word: (char->bool) -> (char->bool) -> Problem.t -> string t
  val variable: (char->bool) -> (char->bool) -> String_set.t
                  -> Problem.t -> string t


  (** {2 Position and State Combinators} *)

  val get_position: (Position.t) t
  val located: 'a t -> 'a Located.t t

  val get_state: State.t t
  val update: (State.t -> State.t) -> unit t


  (** {2 Indentation Combinators} *)
  val absolute: 'a t -> 'a t
  val indented: bool -> 'a t -> 'a t
  val detached: 'a t -> 'a t

  (** {2 Context Combinator} *)
  val in_context: Context_msg.t -> 'a t -> 'a t

  (** {1 Parser} *)

  (** {2 During Parsing} *)

  include PARSER

  (** The state of the parser. *)
  val state: parser -> State.t

  (** {2 Terminated Parser} *)

  (** The result the parser has produced which is either a final value or a
     list of dead ends. Only valid if the parser has terminated. *)
  val result: parser -> (final,error list) result

  (** The list of tokens (i.e. optional characters) which the parser has not
     processed at the point of termination. *)
  val lookahead: parser -> token list



  (** {2 Create and Run the Parser} *)

  (** [make pc st] makes a parser from a parser combinator [pc] and the
     initial state [st]. *)
  val make: final t -> State.t -> parser

  (** [run pc st str] makes a parser from the combinator [pc] and the
     initial state [st] and runs the parser on the string [str]. *)
  val run: final t -> State.t -> string -> parser
end
