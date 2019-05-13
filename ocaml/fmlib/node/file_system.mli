
val mkdir: string -> (unit option -> unit) -> unit
val rmdir: string -> (unit option -> unit) -> unit

val mkdirSync: string -> unit option
val rmdirSync: string -> unit option

val stat: string -> 'a option

val open_: string -> string -> (int option -> unit) -> unit
val close: int -> (unit option -> unit) -> unit

val read:  int -> Io_buffer.t -> (int -> unit) -> unit
val write: int -> Io_buffer.t -> (int -> unit) -> unit
