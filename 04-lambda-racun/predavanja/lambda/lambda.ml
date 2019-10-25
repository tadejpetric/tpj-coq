let read_source filename =
  let channel = open_in filename in
  let source = really_input_string channel (in_channel_length channel) in
  close_in channel; source


let main () =
  if Array.length Sys.argv <> 2
  then failwith ("Run LAMBDA as '" ^ Sys.argv.(0) ^ " <filename>.lam'")
  else
    let filename = Sys.argv.(1) in
    let source = read_source filename in
    let e = Parser.parse source in
    print_endline (Syntax.string_of_exp e);
    Eval.eval e


let _ = main ()
