(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Printf
open Container
open Support

module PC = Proof_context

let usage = "\
usage: alba [-work-dir <path>] [-I <path>] <command> <args>

Commands:
    init           initialize an albatross working directory
    compile        compile a list of modules (default: all modules)
    status         show the compile status of the modules
    help           give help
    version        print version
"


let usage_compile = "\
usage: alba compile [-verbosity <level>] [-force] [<module>...]\n"

let usage_status = "usage: alba status\n"

let usage_init   = "usage: alba init\n"

let usage_help   = "usage: alba help <command>\n"

let alba_version = "v0.1-"

type command =
    Nocommand
  | Compile
  | Init
  | Status
  | Version
  | Help



type state = {
    mutable is_avail:    bool;
    mutable modified:    bool;
    mutable affected:    bool;
    mutable is_new:      bool;
    mutable used:        module_name list
  }


let is_affected (st:state): bool =
  assert (not st.modified || st.affected);
  assert (not st.is_new   || st.affected);
  st.affected


let is_uptodate (st:state): bool = not (is_affected st)


let make_state () = {
  is_avail    = false;
  modified    = false;
  affected    = false;
  is_new      = false;
  used        = []
}




type t = {
    mutable work_dir: string;
    mutable to_compile: int list;
    mutable modules:    int list;
    mutable module_states: (state*state) IntMap.t; (* impl, iface *)
    mutable lib_paths: string list;
    mutable lib_map:   t Library_map.t;  (* lib -> t *)
    mutable command: command;
    mutable trace_proof: bool;
    mutable trace_failed: bool;
    mutable verbosity: int; (* 0: nothing, just errors
                               1: compile status (module, use, verify)
                               2: toplevel (classes, functions, assertions)
                               3: proof trace *)
    mutable force: bool
  }


let basic_lib_paths: string list =
  try
    let str = Sys.getenv "ALBA_LIB_PATH" in
    Mystring.split str ':'
  with Not_found ->
    []



let make (): t = {
  work_dir      = Filename.current_dir_name;
  to_compile    = [];
  modules       = [];
  module_states = IntMap.empty;
  lib_paths     = basic_lib_paths;
  lib_map       = Library_map.empty;
  command       = Nocommand;
  trace_proof   = false;
  trace_failed  = false;
  verbosity = 1;
  force = false;
}


let make_lib (lib_dir:string) (ad:t) = {
  work_dir      = lib_dir;
  to_compile    = [];
  modules       = [];
  module_states = IntMap.empty;
  lib_paths     = ad.lib_paths;
  lib_map       = Library_map.empty;
  command       = Nocommand;
  trace_proof   = false;
  trace_failed  = false;
  verbosity = 0;
  force = false;
}


let my_mkdir (dirname:string): unit =
  try
    Unix.mkdir dirname 0o0755
  with
    Unix.Unix_error _ ->
      raise (Sys_error ("Cannot open directory `" ^ dirname ^ "'"))




let my_stat (fname:string): Unix.stats =
  try
    Unix.stat fname
  with
    Unix.Unix_error _ ->
      raise Not_found




let dir_fold (f: 'a -> string -> 'a) (a:'a) (dirname:string): 'a =
  let arr = Sys.readdir dirname in
  Array.fold_left f a arr



let dir_iter (f:string -> unit) (dirname:string): unit =
  let arr = Sys.readdir dirname in
  Array.iter f arr



let dir_find (f:string -> bool) (dirname:string): string =
  let arr = Sys.readdir dirname in
  let n   = Array.length arr in
  let rec find i =
    if i = n then
      raise Not_found
    else if f arr.(i) then
      arr.(i)
    else
      find (i+1)
  in
  find 0


let dir_has (fn:string) (dirname:string): bool =
  try
    let _ = dir_find (fun n -> n=fn) dirname in
    true
  with Not_found ->
    false



let has_alba_dir (ad:t): bool =
  try
    let alba_dir = Filename.concat ad.work_dir ".alba" in
    Sys.is_directory alba_dir
  with
    Sys_error _ ->
      false


let check_alba_dir (ad:t): unit =
  if has_alba_dir ad then
    ()
  else
    raise (Arg.Bad
             ("working directory `" ^
              ad.work_dir ^ "' is not an albatross directory"))



let find_lib_dir (lib:library_name) (ad:t): string =
  let lib_str = string_of_library lib in
  let rec find (paths:string list): string =
    match paths with
      [] -> raise Not_found
    | path::rest ->
        if dir_has lib_str path then
          Filename.concat path lib_str
        else
          find rest
  in
  find ad.lib_paths



let file_path (mdl:int) (ext:string) (ad:t): string =
  Filename.concat ad.work_dir ((ST.string mdl) ^ "." ^ ext)


let dfile_path (mdl:int) (ext:string) (ad:t): string =
  let alba_dir = Filename.concat ad.work_dir ".alba" in
  Filename.concat alba_dir ((ST.string mdl) ^ ".d" ^ ext)



let file_status (mdlname: int) (ext:string) (ad:t): bool * bool =
  let dfname = dfile_path mdlname ext ad
  and fname  = file_path mdlname ext ad
  in
  let stat = my_stat fname in
  try
    let mstat = my_stat dfname in
    let modified = mstat.Unix.st_mtime < stat.Unix.st_mtime in
      modified, false
  with Not_found ->
    false, true




let used (mdlname:int) (ext:string) (ad:t): module_name list =
  let dfname = dfile_path mdlname ext ad in
  let ch_in = open_in dfname in
  let rec read (lst:module_name list): module_name list =
    try
      let str = input_line ch_in in
      match Mystring.rev_split str '.' with
        [] -> assert false
      | str::libstr ->
          let nme = ST.symbol str
          and lib = List.rev_map ST.symbol libstr
          in
          read ((nme,lib)::lst)
    with End_of_file ->
      lst
  in
  let lst = read [] in
  close_in ch_in;
  List.rev lst




let module_states (ad:t): (state*state) IntMap.t =
  let state (mdlname:int) (ext:string): state =
    let st = make_state () in
    try
      let modi,is_new = file_status mdlname ext ad in
      st.is_avail <- true;
      st.modified <- modi;
      st.is_new   <- is_new;
      st.affected <- is_new || modi;
      if not modi && not is_new then
        st.used <- used mdlname ext ad;
      st
    with
      Not_found -> st
  in
  List.fold_left
    (fun map nme ->
      if IntMap.mem nme map then
        map
      else
        let st  = state nme "al"
        and sti = state nme "ali"
        in
        if st.affected && sti.is_avail then
          sti.affected <- true;
        IntMap.add nme (st,sti) map)
    IntMap.empty
    ad.modules




let get_module_states (ad:t): unit =
  (* Read the names of all source files (.al,.ali), compile a list of all
     modules in the package, get the states of all modules (new, modified,
     unchanged) and mark the modules which are affected indirectly.  *)
  assert (has_alba_dir ad);
  let f1 (set:IntSet.t) (fn:string): IntSet.t =
    try
      let mdlstr =
        if Filename.check_suffix fn ".al" then
          Filename.chop_suffix fn ".al"
        else if Filename.check_suffix fn ".ali" then
          Filename.chop_suffix fn ".ali"
        else
          raise Not_found
      in
      IntSet.add (ST.symbol mdlstr) set
    with Not_found ->
      set
  and check_affected (nme:int) (st:state): unit =
    List.iter
      (fun (used,lib) ->
        if lib <> [] then
          () (* nyi: libraries *)
        else
          try
            let _,stui = IntMap.find used ad.module_states in
            if not stui.is_avail || stui.modified || stui.is_new then
              st.affected <- true
          with Not_found ->
            st.affected <- true)
      st.used
  in
  let set = dir_fold f1 IntSet.empty ad.work_dir in
  ad.modules <- IntSet.elements set;
  ad.module_states <- module_states ad;
  IntMap.iter
    (fun nme (st,sti) ->
      check_affected nme st;
      check_affected nme sti)
    ad.module_states




let find_lib_ad (lib:library_name) (ad:t): t =
  if lib = [] then
    ad
  else
    try
      Library_map.find lib ad.lib_map
    with Not_found ->
      let dirname = find_lib_dir lib ad in
      let lib_ad  = make_lib dirname ad in
      if has_alba_dir lib_ad then begin
        get_module_states lib_ad;
        ad.lib_map <- Library_map.add lib lib_ad ad.lib_map;
        lib_ad
      end else
        raise Not_found




let check_no_command (str:string) (ad:t): unit =
  match ad.command with
    Nocommand -> ()
  | _ -> raise (Arg.Bad str)


let check_compile (str:string) (ad:t): unit =
  match ad.command with
    Compile -> ()
  | _ -> raise (Arg.Bad str)



let set_work_dir (ad:t) (str:string): unit =
  check_no_command "unknown option `-work-dir'" ad;
  let len = String.length str in
  assert (0 < len);
  let str = if str.[len-1] <> '/' then str ^ "/" else str in
  ad.work_dir <- str





let add_lib_path (ad:t) (str:string): unit =
  check_no_command "unknown option `-I'" ad;
  ad.lib_paths <- str :: ad.lib_paths



let trace_proof (ad:t) (): unit =
  ad.trace_proof <-  true



let trace_failed (ad:t) (): unit =
  ad.trace_failed <-  true



let set_verbosity (ad:t) (level:int): unit =
  check_compile "unknown option `-verbosity'" ad;
  if 0 <= level then
    ad.verbosity <- level


let set_force (ad:t) (): unit =
  check_compile "unknown option `-force" ad;
  ad.force <- true


let set_argument (ad:t) (str:string): unit =
  let illegal (): unit =
    raise (Arg.Bad ("Illegal argument `" ^ str ^ "'")) in
  match ad.command with
    Nocommand ->
      if str = "compile" then
        (check_alba_dir ad;
         ad.command <- Compile)
      else if str = "status" then
        (check_alba_dir ad;
        ad.command <- Status)
      else if str = "init" then
        ad.command <- Init
      else if str = "help" then
        ad.command <- Help
      else if str = "version" then
        ad.command <- Version
      else
        raise (Arg.Bad ("unknown command `" ^ str ^ "'"))
  | Compile ->
      let mdl = ST.symbol str in
      if not (List.mem mdl ad.to_compile) then
        ad.to_compile <- (ST.symbol str) :: ad.to_compile
  | Status ->
      illegal ()
  | Init ->
      illegal ()
  | Version ->
      assert false (* cannot happen *)
  | Help ->
      if str = "compile" then
        (printf "%s" usage_compile; exit 0)
      else if str = "init" then
        (printf "%s" usage_init; exit 0)
      else if str = "status" then
        (printf "%s" usage_status; exit 0)
      else if str = "help" then
        (printf "%s" usage_help; exit 0)
      else
        raise (Arg.Bad ("unknown command `" ^ str ^ "'"))




let make_from_arguments (): t =
  let do_nothing (): unit = () in
  let ad = make () in
  Arg.parse
    [("-work-dir", Arg.String (set_work_dir ad), "");
     ("-I",        Arg.String (add_lib_path ad), "");
     ("-trace-proof",        Arg.Unit (trace_proof ad), "");
     ("-trace-failed-proof", Arg.Unit (trace_failed ad), "");
     ("-verbosity", Arg.Int  (set_verbosity ad),"");
     ("-force",    Arg.Unit  (set_force ad),"");
     ("-help",     Arg.Unit  do_nothing,        "");
     ("--help",    Arg.Unit  do_nothing,        "");
   ]
    (set_argument ad)
    "";
  (match ad.command with
    Nocommand ->
      printf "%s" usage;
      exit 0
  | Compile
  | Status ->
      check_alba_dir ad;
      get_module_states ad
  | _ ->
      ());
  ad



let alba_init (ad:t): unit =
  (*let dirname = ad.work_dir ^ ".alba/" in*)
  let dirname = Filename.concat ad.work_dir ".alba" in
  try
    my_mkdir dirname
  with
    Sys_error _ ->
      dir_iter
        (fun fn ->
          if Filename.check_suffix fn ".dal" || Filename.check_suffix fn ".dali"
          then
            Sys.remove  (Filename.concat dirname fn))
        dirname





let alba_status (ad:t): unit =
  let pr_state (mdlname: int) (st:state) (ext:string): unit =
    let str =
      if st.is_new then        "new:     "
      else if st.modified then "modified:"
      else if st.affected then "affected:"
      else "" in
    if str <> "" then
      printf "\t%s %s.%s\n" str (ST.string mdlname) ext
  in
  IntMap.iter
    (fun mdlname (st,sti) ->
      pr_state mdlname st "al";
      pr_state mdlname sti "ali")
    ad.module_states





let abort (str:string) =
  prerr_string (str ^ "\n"); exit 1




let info_abort (fn:string) (info:Support.info) (str:string) =
  abort ((Support.info_string fn info) ^ " " ^ str)




type 'a parse_fun = (Lexing.lexbuf  -> Parser.token) -> Lexing.lexbuf -> 'a


let parse (fn:string) (parse_function: 'a parse_fun): 'a =
  try
    Lexer.reset ();
    let ch_in = open_in fn in
    let lexbuf = Lexing.from_channel ch_in in
    let res = parse_function Lexer.token lexbuf in
    close_in ch_in;
    res
  with
    Parsing.Parse_error ->
      info_abort fn (Lexer.info_of_last_pos ()) "Unexpected token"
  | Support.Error_info (info,str) ->
      info_abort fn info str
  | Sys_error str ->
      abort str



let parse_use_block (fn:string): Support.use_block =
  parse fn Parser.use_block_opt



let parse_file (fn:string): use_block * declaration list =
  parse fn Parser.file


let file_path_used (um:module_name withinfo) (fn:string) (ad:t): string =
  let m,lib = um.v in
  if lib = [] then
    file_path m "ali" ad
  else
    try
      let lib_ad = find_lib_ad lib ad in
      file_path m "ali" lib_ad
    with Not_found ->
        info_abort fn um.i ("library `" ^ (string_of_library lib) ^ "' not found")




let find (mdl:int) (ad:t): state*state =
  try
    IntMap.find mdl ad.module_states
  with Not_found ->
    abort ("module `" ^ (ST.string mdl) ^ "' does not exist")




let analyze (ast:declaration list) (fn:string) (pc:PC.t): unit =
  try
    Ast.analyze ast pc
  with Error_info (info,str) ->
    info_abort fn info str


let analyze_used
    (fn:string) (mdl:int) (use_blk: use_block) (pc:PC.t) (ad:t)
    : IntSet.t =
  (* Parse all directly and indirectly used modules of [use_blk] of the module
     [mdl] within the file [fn] and return the complete set of all used modules.  *)
  let mt = PC.module_table pc
  in
  assert (List.for_all
            (fun m -> let nme,lib = m.v in lib <> [] || nme <> mdl)
            use_blk);
  let rec used (stack:(module_name withinfo*string*string*use_block) list)
      (set:IntSet.t)
      (fn_outer:string)
      : IntSet.t =
    let push (umdl:module_name withinfo) (fn:string)
        : (module_name withinfo*string*string*use_block) list =
      if List.exists (fun (m,_,_,_) -> m.v=umdl.v) stack then
        info_abort fn umdl.i
          ("circular module usage [" ^
           (String.concat ","
              (List.map
                 (fun (m,_,_,_) -> string_of_module m.v)
                 (List.rev ((umdl,"","ali",[])::stack)))) ^
           "]")
      else
        let m,lib = umdl.v in
        let fn = file_path_used umdl fn ad in
        let use_blk = parse_use_block fn in
        let use_blk =
          if lib=[] then use_blk
          else List.map
              (fun mdl ->
                let m,l = mdl.v in
                if l=[] then withinfo mdl.i (m,snd umdl.v) else mdl)
              use_blk
        in
        (umdl, fn, "ali", use_blk) :: stack
    in
    match stack with
      [] -> assert false
    | (mdl,fn,ext,use_blk)::rest ->
        assert (ext="ali" || rest=[]);
        try
          let umdl =
            List.find (fun m -> not (Module_table.has m.v mt)) use_blk
          in
          used (push umdl fn) set fn
        with Not_found ->
          if ext="al" then set
          else begin
            if 1 < ad.verbosity then
              printf " use `%s'\n" (string_of_module mdl.v);
            let mt = Proof_context.module_table pc in
            let nme = fst mdl.v in
            if Module_table.has_base nme mt then
              info_abort fn_outer mdl.i ("Duplicate base module " ^ (ST.string nme));
            PC.add_used_module mdl.v set pc;
            let use_blk2,ast = parse_file fn in
            analyze ast fn pc;
            let set = IntSet.add (Module_table.current mt) set in
            used rest set fn
          end
  in
  let mdl = withinfo UNKNOWN (mdl,[]) in
  used [mdl,fn,"al",use_blk] IntSet.empty fn


let update_depend (nme:int) (pub:bool) (pc:PC.t) (ad:t): unit =
  let mt = PC.module_table pc in
  let used, fn =
    if pub then
      Module_table.current_used mt,
      dfile_path nme "ali" ad
    else
      Module_table.current_used_priv mt,
      dfile_path nme "al" ad
  in
  try
    let nmestr = ST.string nme in
    let ch = open_out fn in
    IntSet.iter
      (fun m ->
        let str = Module_table.name m mt in
        if str <> nmestr then
          output_string ch (str ^ "\n"))
      used;
    close_out ch
  with Sys_error str ->
    abort str


let verify_interface (nme:int) (pc:PC.t) (ad:t): unit =
  if 1 < ad.verbosity then
    printf " verify interface `%s'\n" (ST.string nme);
  let fn = file_path nme "ali" ad      in
  let use_blk,ast = parse_file fn      in
  let mt = PC.module_table pc in
  begin try
    let used = Module_table.interface_used use_blk mt in
    PC.set_interface_check used pc
  with Error_info(info,str) ->
    info_abort fn info str
  end;
  analyze ast fn pc;
  update_depend nme true pc ad




let verify_implementation (nme:int) (pc:PC.t) (ad:t): unit =
  let fn = file_path nme "al" ad        in
  let use_blk = parse_use_block fn      in
  let used = analyze_used fn nme use_blk pc ad in
  if 1 < ad.verbosity then
    printf " verify implementation `%s'\n" (ST.string nme);
  let use_blk2,ast = parse_file fn      in
  assert (use_blk = use_blk2);
  PC.add_current_module nme used pc;
  analyze ast fn pc;
  update_depend nme false pc ad



let compile (ad:t): unit =
  let rec comp
      (work:int list)
      (stack:(int*state*state) list)
      (ready:int list)
      : unit =
    let push_and_comp
        (mdl:int)
        (work:int list)
        (stack:(int*state*state) list)
        : unit =
      assert (not (List.mem mdl ready));
      if List.exists (fun (m,_,_) -> m=mdl) stack then
        let stck = List.map (fun (m,_,_) -> m) stack in
        abort
          ("circular module usage [" ^
           (String.concat "," (List.rev_map ST.string (mdl::stck))) ^
          "]")
      else
        let st,sti = find mdl ad in
        if not (is_affected st) && not (is_affected sti)
        then(
          comp work stack (mdl::ready))
        else begin
          if st.is_new || st.modified then begin
            let used = parse_use_block (file_path mdl "al" ad) in
            st.used <- List.map (fun mdl -> mdl.v) used
          end;
          comp work ((mdl,st,sti)::stack) ready
        end
    in
    match work,stack with
      [], []        -> ()
    | mdl::rest, [] ->
        if List.mem mdl ready then
          comp rest stack ready
        else
          push_and_comp mdl rest stack
    | _,  (mdl,st,sti)::rest ->
        try
          let umdl =
            List.find (fun (m,lib) -> lib = [] && not (List.mem m ready))
              st.used
          in
          assert (snd umdl = []);
          push_and_comp (fst umdl) work stack
        with Not_found ->
          if 0 < ad.verbosity then begin
            printf "Compile module `%s'\n" (ST.string mdl);
            flush_all ()
          end;
          let pc = PC.make ad.verbosity in
          verify_implementation mdl pc ad;
          if sti.is_avail then
            verify_interface mdl pc ad;
          comp work rest (mdl::ready)
  in
  comp ad.to_compile [] []



let alba_compile (ad:t): unit =
  ad.to_compile <- List.rev ad.to_compile;
  if ad.to_compile = [] then
    ad.to_compile <- ad.modules;
  if ad.force then
    List.iter
      (fun mdl ->
        let st,sti = find mdl ad in
        st.affected <- true;
        sti.affected <- true)
      ad.to_compile;
  compile ad



let _ =
  let ad = make_from_arguments () in
  match ad.command with
    Nocommand ->
      printf "%s" usage;
  | Init ->
      alba_init ad
  | Status ->
      alba_status ad
  | Compile ->
      alba_compile ad
  | Version ->
      printf "version %s\n" alba_version; exit 0
  | Help ->
      printf "%s" usage_help
