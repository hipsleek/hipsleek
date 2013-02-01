// ocfg.g - grammar for ordered context grammar -*- ocfg -*-
        
// white = '\009' | '\011' | '\012' | '\032';
// comment = '//';
// newline = '\013' | '\010' | '\013\010';
// 
// digit = '0'-'9';
// int = digit+;
// letter = 'A'-'Z' | 'a'-'z';
// alpha = letter | digit | '_';
// id = letter alpha*;
// literal = '\'' -- '\'';
// str = '\"' -- '\"';


g: r+ f*;                               // grammar

x: _ident;                              // identifier
q: _char;                               // literal

r:                                      // rule
= Alias: x ':' '#'? u+ ';'
| Union: x ':' '#'? p+ ';'
;

f: '-' x ':' q ';';                     // filter

a:                                      // associativity
= Non: '='
| Left: '<'
| Right: '>'
;

p: a c ++ '|';                          // group
c: x ':' u*;                            // case

u:                                      // item
= Literal: q
| Ident: x
| Marker: q '?'
| Option: x '?'
| Star: x '*'
| Plus: x '+'
| Sstar: x '**' q
| Pplus: x '++' q
;
