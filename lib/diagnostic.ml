open Location

type diagnostic_sink = {
  mutable num_errors: int;
}

type diagnostic_type = Info | Warning | Error

let make_diagnostic_sink () : diagnostic_sink = { num_errors = 0; }

let string_of_diagnostic_type (typ: diagnostic_type) = match typ with
  | Info -> "Info"
  | Warning -> "Warning"
  | Error -> "Error"

let output_diagnostic (sink: diagnostic_sink) (typ: diagnostic_type) (loc: location) (msg: string) : unit =
  Printf.printf "%s %s: %s\n" (string_of_diagnostic_type typ) (string_of_location loc) msg;
  sink.num_errors <- sink.num_errors + 1
