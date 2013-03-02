let file_list: string list ref = ref []

let clear () = file_list := []

let add str = file_list := str::!file_list

let usage_string = "\
Usage: eiffelc options file1.e file2.e ...
       eiffelc options filelist.eml"

let parse_module_list ml =
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
         raise (Support.Exit_error ""))
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
  let _ = clear ()
  in
  let _ = Arg.parse [] add usage_string
  in
  if List.for_all (fun fn -> Filename.check_suffix fn ".e") !file_list then
    List.rev !file_list
  else
    match !file_list with
      [fn] ->
        if Filename.check_suffix fn ".eml" then
          parse_module_list fn
        else
           raise (Support.Exit_error usage_string)
    | _ ->
        raise (Support.Exit_error usage_string)

