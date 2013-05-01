let usage_string = "\
Usage: 
    eiffelc options file1.e file2.e ...  pckg.epc
    eiffelc options filelist.eml [pckg.epc]

    options
       -I path    directory to search for used packages"

let display_usage str =  raise (Support.Exit_error (str^usage_string))



let parse_eml_file ml =
  let dir = Filename.dirname ml
  and ic = open_in ml
  in
  let rec scan line_no list =
    let line = input_line ic
    in
    try
      if Filename.check_suffix line ".e" then
        scan (line_no+1) (line::list)
      else
        (Printf.eprintf "%s:%d: %s does not have extension \".e\"\n"
           ml line_no line;
         display_usage "")
    with
      End_of_file -> line::list
  in
  List.rev_map 
    (fun e ->
      if (String.length e)>0 && e.[0]!='/' 
      then dir ^ "/" ^ e
      else e)
    (scan 1 [])


let parse () =
  let efiles:    string list ref = ref []
  and emlfiles:  string list ref = ref []
  and pfiles:    string list ref = ref []
  and includes:  string list ref = ref []
  in

  let add_file fn    = 
    if Filename.check_suffix fn ".e" then
      efiles := fn::!efiles
    else if Filename.check_suffix fn ".eml" then
      emlfiles := fn::!emlfiles
    else if Filename.check_suffix fn ".epc" then
      pfiles := fn::!pfiles
    else
      display_usage ("error: file \"" ^ fn ^ "\" has illegal extension\n")
  and add_include str = includes  := str::!includes
  in

  let _ = 
    Arg.parse 
      [("-I",Arg.String add_include,"path to search for packages")]
      add_file 
      usage_string
  in

  if !efiles!=[] && !emlfiles=[] 
  then
    match !pfiles with
      [pfn] -> 
        !includes, List.rev !efiles, pfn
    | [] -> display_usage "error: packagefile needed\n"
    | _  -> display_usage "error: only one packagefile allowed\n"
  else if !efiles=[] &&  !emlfiles!=[]
  then
    let eml = 
      match !emlfiles with 
        [fn] -> fn
      | _ ->     display_usage "error: only one eml file allowed\n"
    in
    let pfn =
      match !pfiles with
        [] -> (Filename.chop_extension eml) ^ ".epc"
      | [fn] -> fn
      | _ -> display_usage "error: only one packagefile allowed\n"
    in
    !includes, parse_eml_file eml, pfn
  else
    display_usage "error: either explicit list of modules or .eml file\n"

