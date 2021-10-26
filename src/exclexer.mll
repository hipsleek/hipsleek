{
  open Globals
  open Iparser

  let comment_level = ref (0 : int)

  let java_bcount = ref (0 : int)
  let java_code = Buffer.create 100

  let incr_linenum file_name lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
      lexbuf.Lexing.lex_curr_p <- 
	{ pos with
	    Lexing.pos_fname = file_name;
	    Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
	    Lexing.pos_bol = pos.Lexing.pos_cnum;
	}

  let print_error lexbuf msg =
	let pos = lexbuf.Lexing.lex_curr_p in
	  Error.report_error {Error.error_loc = pos;
						  Error.error_text = msg}

  let keywords = Hashtbl.create 100
  let _ = List.map (fun (k, t) -> Hashtbl.add keywords k t)
	[("assert", ASSERT);
	 ("assume", ASSUME);
	 ("bind", BIND);
	 ("bool", BOOL);
	 ("break", BREAK);
	 ("class", CLASS);
	 (* ("coercion", COERCION); *)
	 ("conseq", CONSEQ);
	 ("const", CONST);
	 ("continue", CONTINUE);
	 ("data", DATA);
	 ("debug", DDEBUG);
	 ("diff", DIFF);
	 ("dynamic", DYNAMIC);
	 ("else", ELSE);
	 ("ensures", ENSURES);
   ("ensures_exact", ENSURES_EXACT);
   ("ensures_inexact", ENSURES_INEXACT);
	 ("enum", ENUM);
	 ("ex", EXISTS);
	 ("exists", EXISTS);
	 ("extends", EXTENDS);
	 ("false", FALSE);
	 ("float", FLOAT);
	 ("fold", FOLD);
	 ("forall", FORALL);
	 ("if", IF);
	 ("implies", IMPLIES);
	 ("import", IMPORT);
	 ("in", IN);
	 ("int", INT);
	 ("intersect", INTERSECT);
	 ("inv", INV);
     ("lemma", LEMMA);
	 ("max", MAX);
	 ("min", MIN);
	 ("bagmax", BAGMAX);
	 ("bagmin", BAGMIN);
	 ("new", NEW);
	 ("notin", NOTIN);
	 ("null", NULL);
	 ("off", OFF);
	 ("on", ON);
	 ("or", ORWORD);
	 ("dprint", PRINT);
	 ("ref", REF);
	 ("requires", REQUIRES);
	 ("res", RES "res");
	 ("return", RETURN);
	 ("self", SELF "self");
	 ("split", SPLIT);
	 ("subset", SUBSET);
	 ("static", STATIC);
	 ("then", THEN);
	 ("this", THIS "this");
	 ("to", TO);
	 ("true", TRUE);
	 ("unfold", UNFOLD);
	 ("union", UNION);
	 ("view", VIEW);
	 ("void", VOID);
	 ("where", WHERE);
	 ("while", WHILE)]
}

let alpha = ['a'-'z' 'A'-'Z' '_']
let digit = ['0'-'9']
let intnum = digit+
let fnum = digit*('.')digit+
let whitespace = [' ' '\t']

rule tokenizer file_name = parse
  | "/*" { 
	  comment_level := 0;
	  comment file_name lexbuf 
	}
  | "//" { line_comment file_name lexbuf }
  | '&' { AND }
  | "&&" { ANDAND }
  | "@" { AT }
  | '}' { CBRACE }
  | ':' { COLON }
  | "::" { COLONCOLON }
  | ',' { COMMA }
  | ')' { CPAREN }
  | ']' { CSQUARE }
  | '$' { DOLLAR }
  | "." { DOT }
  | "\"" { DOUBLEQUOTE }
  | "=" { EQ }
  | "==" { EQEQ }
  | "<-" { RIGHTARROW }
  | "<->" { EQUIV }
  | '>' { GT }
  | ">=" { GTE }
  | '#' { HASH }
  | "=>" { IMPLY }
  | "->" { LEFTARROW }
  | '<' { LT }
  | "<=" { LTE }
  | "-" { MINUS }
  | "!=" { NEQ }
  | "!" { NOT }
  | '{' { OBRACE }
  | '(' { OPAREN }
  | "+=" { OP_ADD_ASSIGN }
  | "--" { OP_DEC }
  | "/=" { OP_DIV_ASSIGN }
  | "++" { OP_INC }
  | "%=" { OP_MOD_ASSIGN }
  | "*=" { OP_MULT_ASSIGN }
  | "-=" { OP_SUB_ASSIGN }
  | '|' { OR }
  | "||" { OROR }
  | '[' { OSQUARE }
  | '%' { PERCENT }
  | '+' { PLUS }
  | '\'' { PRIME }
  | ';' { SEMICOLON }
  | '*' { STAR }
  | intnum as numstr { LITERAL_INTEGER (int_of_string numstr) }
  | fnum as numstr { LITERAL_FLOAT (float_of_string numstr) }
  | alpha(alpha | digit)* as idstr 
	  {
		if idstr = "_" then
			begin
				IDENTIFIER ("Anon_" ^ fresh_name ())
		  end
		else if idstr = "java" then begin
		  pre_java file_name lexbuf (* search for the first opening brace *)
		end else
		  try Hashtbl.find keywords idstr
		  with | _ -> IDENTIFIER idstr
	  }
  | whitespace { tokenizer file_name lexbuf }
  | '\n' { incr_linenum file_name lexbuf; tokenizer file_name lexbuf }
  | '\r' { incr_linenum file_name lexbuf; tokenizer file_name lexbuf }
  | "\r\n" { incr_linenum file_name lexbuf; tokenizer file_name lexbuf }
  | eof { EOF }

(* search for the first open brace following java keyword *)
and pre_java file_name = parse 
  | "{" {
	  java_bcount := 0;
	  Buffer.clear java_code;
	  java file_name lexbuf
	}
  | whitespace { pre_java file_name lexbuf }
  | _ { print_error lexbuf "java keyword must be followed by Java code enclosed in {}" }

and java file_name = parse
  | "}" {
	  if !java_bcount = 0 then
		JAVA (Buffer.contents java_code)
	  else begin
		java_bcount := !java_bcount - 1;
		Buffer.add_char java_code '}';
		java file_name lexbuf
	  end
	} 
  | "{" {
	  java_bcount := !java_bcount + 1;
	  Buffer.add_char java_code '{';
	  java file_name lexbuf
	}
  | '\n' { 
	  incr_linenum file_name lexbuf; 
	  Buffer.add_char java_code '\n'; 
	  java file_name lexbuf 
	}
  | '\r' { 
	  incr_linenum file_name lexbuf; 
	  Buffer.add_char java_code '\r'; 
	  java file_name lexbuf 
	}
  | "\r\n" {
	  incr_linenum file_name lexbuf; 
	  Buffer.add_string java_code "\r\n";
	  java file_name lexbuf 
	}
  | _ as c  { 
	  Buffer.add_char java_code c;
	  java file_name lexbuf 
	}


and comment file_name = parse
  | "*/" { 
	  if !comment_level = 0 then
		tokenizer file_name lexbuf 
	  else begin
		comment_level := !comment_level - 1;
		comment file_name lexbuf
	  end
	}
  | "/*" {
	  comment_level := !comment_level + 1;
	  comment file_name lexbuf
	}
  | '\n' { incr_linenum file_name lexbuf; comment file_name lexbuf }
  | '\r' { incr_linenum file_name lexbuf; comment file_name lexbuf }
  | "\r\n" { incr_linenum file_name lexbuf; comment file_name lexbuf }
  | _  { comment file_name lexbuf }

and line_comment file_name = parse
  | '\r' | '\n' | "\r\n" { incr_linenum file_name lexbuf; tokenizer file_name lexbuf }
  | _ { line_comment file_name lexbuf }

and preprocess pfile = parse
  | "import" 
      {
		(* processing import *)
		let _ = rip_ws lexbuf in
		let tmp_file_name = get_file_name lexbuf in
		let file_name = String.sub tmp_file_name 1 (String.length tmp_file_name - 2) in
		let in_file = open_in file_name in
		let cont = ref true in
		let in_cont = Buffer.create 1024 in
		  while !cont do
			try
			  let line = input_line in_file in
				Buffer.add_string in_cont (line ^ "\n")
			with
			  | End_of_file -> cont := false
		  done;
		  output_string pfile (Buffer.contents in_cont);
		  preprocess pfile lexbuf
      }
  | _ as c 
      { (* other character, just copy it over *)
		output_char pfile c;
		preprocess pfile lexbuf
		  
      }
  | eof {  } 

and rip_ws = parse 
  | (' ' | '\t')+ as ws { ws }
  | _  { print_string "There must be whitespace after import directive\n"; exit (-1) }

and get_file_name = parse
  | '\"'([^ '\n' '\"'])+'\"' as fn { fn }
  | _ { print_string "file name following import must be enclosed in double quotes\n"; exit (-1) }
