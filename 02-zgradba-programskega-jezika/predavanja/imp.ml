let read_whole_file filename =
    let channel = open_in filename in
    let str = really_input_string channel (in_channel_length channel) in
    close_in channel;
    str
in
let source = read_whole_file "example.imp" in
let cmd = Parser.parse Parser.cmd source in
match Check.check_cmd [] cmd with
| None -> print_endline "Error"
| Some _ ->
    let env = Eval.initial_environment in
    let env' = Eval.eval_cmd env cmd in
    Eval.print_environment env'
