(* https://github.com/yurug/menhir-error-recovery/blob/master/parse.ml *)
open Ast
open Diagnostic
open Location
open Parser.Incremental
open Parser.MenhirInterpreter
open LexPass
open Token

let rec truncate_until (f : ltoken -> bool) (tokens : ltoken list) = match tokens with
  | [] -> []
  | h::t when f h -> h::t
  | _::t -> truncate_until f t

let recover_from_error last_reduction (error_token : ltoken) (tokens : ltoken list) (checkpoint : statement checkpoint) =
  match last_reduction with
  | `ExpectStatement last_checkpoint ->
    let tokens = if last_checkpoint == checkpoint then tokens else error_token::tokens in
    let tokens = truncate_until (function
      | Parser.EOF, _, _
      | Parser.SEMI, _, _
      | Parser.RCURLY, _, _ -> true
      | _ -> false) tokens in
    let tokens = match tokens with
      | (Parser.SEMI, _, _) :: t -> t
      | _ -> tokens in
    (tokens, last_checkpoint)

let update_last_reduction (checkpoint : statement checkpoint) (production : production) last_reduction =
  match lhs production with
    | X (N N_stat)
    | X (N N_expect_stat) -> `ExpectStatement checkpoint
    | _ -> last_reduction

let parse_recovering (sink: diagnostic_sink) (tokens : ltoken list) : statement =
  let rec on_error last_reduction (error_ltoken : ltoken) (tokens : ltoken list) checkpoint =
    let (error_token, a, b) = error_ltoken in
    output_diagnostic sink Error (make_location a b) (Printf.sprintf "unexpected %s" (string_of_token error_token));
    recover_from_error last_reduction error_ltoken tokens checkpoint

  and run last_reduction (input_needed_cp : statement checkpoint) (offered_token : ltoken option) (tokens : ltoken list) (checkpoint : statement checkpoint) : statement =
    match checkpoint, tokens with
    | InputNeeded _, h::t -> run last_reduction checkpoint (Some h) t (offer checkpoint h)
    | InputNeeded _, [] -> raise Parsing.Parse_error
    | Accepted x, _ -> x
    | Rejected, _
    | HandlingError _, _ -> 
      (match offered_token with
        | Some (Parser.EOL, _, _) -> run last_reduction input_needed_cp None tokens input_needed_cp
        | Some offered_token ->
          let recovery_tokens, recovery_cp = on_error last_reduction offered_token tokens input_needed_cp in
          run last_reduction input_needed_cp None recovery_tokens recovery_cp
        | None -> assert false)
    | Shifting _, _ -> run last_reduction input_needed_cp offered_token tokens (resume checkpoint)
    | AboutToReduce (_, production), _ -> run
      (update_last_reduction input_needed_cp production last_reduction)
      input_needed_cp
      offered_token
      tokens
      (resume checkpoint)
  in
  let initial_position = match tokens with [] -> null_position | (_, position, _)::_ -> position in
  let initial_checkpoint = main { pos_fname = initial_position.pos_fname; pos_lnum = 1; pos_cnum = 0; pos_bol = 0} in
  run (`ExpectStatement initial_checkpoint) initial_checkpoint None tokens initial_checkpoint
