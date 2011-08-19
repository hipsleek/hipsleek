
 let string_of_entailment (e: entailment) =
    Printf.sprintf "(%d,%d): %s" e.pos.start_line e.pos.stop_line e.name
