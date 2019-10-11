let read_source filename =
  let channel = open_in filename in
  let source = really_input_string channel (in_channel_length channel) in
  close_in channel; source


let main () =
  if Array.length Sys.argv <> 2
  then failwith ("Run IMP as '" ^ Sys.argv.(0) ^ " <filename>.imp'")
  else
    let filename = Sys.argv.(1) in
    let source = read_source filename in
    let cmd = Parser.parse source in
    if Check.check cmd
    then Eval.run cmd
    else failwith "Not all locations are set!"


let _ = main ()
