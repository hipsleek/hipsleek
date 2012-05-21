type triary_bool =
	| True
	| False
	| Unknown

let string_of_triary_bool b = match b with
	| True -> "true"
	| False -> "false"
	| Unknown -> "unknown"

let negate_triary b = match b with
	| True -> False
	| False -> True
	| Unknown -> Unknown