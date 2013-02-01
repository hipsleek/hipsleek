// java.g - java grammar -*- ocfg -*-

// # for line info for debugging 
// = for non-associative, < for left-associative, > for right-associative
// ? for optional, * for zero-or-more repetition, + for one-or-more repetition
// ** q for zero-or-more repetition with the separator q
// ++ q for one-or-more repetition with the separator q

cunit: package? import* decl*;          // compilation unit
package: # 'package' name ';';          // package declaration
import: # 'import' 'static'? name all? ';';

name: id ++ '.';                        // qualified name
id: _ident;                         
all: '.' '*';

decl: #                                 // type declaration
= Class: modifier* 'class' id tparams? extend? implements? bodies
| Iface: modifier* 'interface' id tparams? extends? bodies
| Enum: modifier* 'enum' id implements? '{' enumbody '}'
| Annot: modifier* '@' 'interface' id bodies
| Empty: ';'
;

tparams: '<' tparam ++ ',' '>';         // type parameter list
tparam: id extend? tinter*;             // type parameter
tinter: '&' ty;                         // intersection type
targs: '<' wty ++ ',' '>';              // type arguments

wty:                                    // wildcard type
= WildType: ty
| WildCard: '?'
| WildExtends: '?' 'extends' ty
| WildSuper: '?' 'super' ty
;

extend: 'extends' ty;                   // class extension
extends: 'extends' ty ++ ',';           // class extension list
implements: 'implements' ty ++ ',';     // interface implement list

ty:                                     // types
= Tarray: ty dimen+                     // array
= Tinst: ty targs                       // instantiation
= Tname: name
| Tbool: 'boolean'
| Tbyte: 'byte'
| Tchar: 'char'
| Tdouble: 'double'
| Tfloat: 'float'
| Tint: 'int'
| Tlong: 'long'
| Tshort: 'short'
| Tvoid: 'void'
;

dimen: '[' ']';
size: '[' exp ']';

body: #                                 // class body
= Init: 'static'? block                 // initialization
| Inner: decl                           // inner declaration
| Ctor: modifier* tparams? id signat block // constructor
| MethodNone: modifier* tparams? ty id signat ';' // empty method 
| MethodSome: modifier* tparams? ty id signat block // method with body
| Field: modifier* ty vdecl ++ ',' ';' // field
;

enumbody:
= EnumNone: enumconst ++ ',' ','? ';'?  // without class body
| EnumSome: enumconst ++ ',' ','? ';' body+ // with class body
;

enumconst: modifier* id arg? bodies?;   // enumeration constant
bodies: '{' body* '}';

signat: '(' formals ')' adefault? dimen* throws?;
adefault: 'default' exp;                 // annotation default
arg: '(' exp ** ',' ')';                // argument
labelexp: id '=' exp;                   // labelled expression
vdecl: id dimen* vinit?;                // variable declaration
vinit: '=' exp;                        // variable initialization

stmt: #
> ForDecl: 'for' '(' modifier* ty vdecl ++ ',' ';' exp? ';' exp ** ',' ')' stmt
| ForEach: 'for' '(' modifier* ty id ':' exp ')' stmt
| ForExp: 'for' '(' exp ** ',' ';' exp? ';' exp ** ',' ')' stmt
| While: 'while' '(' exp ')' stmt
| If: 'if' '(' exp ')' stmt ifelse?
| Label: id ':' stmt
= AssertNone: 'assert' exp ';'
| AssertSome: 'assert' exp ':' exp ';'
| Block: block
| Break: 'break' id? ';'
| Case: 'case' exp ':'
| Continue: 'continue' id? ';'
| Vdecl: modifier* ty vdecl ++ ',' ';'
| Default: 'default' ':'
| Do: 'do' stmt 'while' '(' exp ')' ';'
| Exp: exp ';'
| Local: decl
| Return: 'return' exp? ';'
| Switch: 'switch' '(' exp ')' block
| Sync: 'synchronized' '(' exp ')' block
| Throw: 'throw' exp ';'
| Try: 'try' block catch* tfinally?
;

formals: 
> ArgMore: modifier* ty id dimen* ',' formals
= ArgFix: modifier* ty id dimen*
| ArgVar: modifier* ty '...' id dimen*
| ArgNone:
;

ifelse: 'else' stmt;
block: '{' stmt* '}';
catch: 'catch' '(' modifier* ty id ')' block;
tfinally: 'finally' block;
throws: 'throws' name ++ ',';

exp: #                                  // expressions
= Escape: '\\' exp
= Array: '{' exps '}'
> Assign: exp assign exp
> Cond: exp '?' exp ':' exp
< Cor: exp '||' exp
< Cand: exp '&&' exp
< Or: exp '|' exp
< Xor: exp '^' exp
< And: exp '&' exp
< Eq: exp '==' exp
| Ne: exp '!=' exp
< Lt: exp '<' exp
| Gt: exp '>' exp
| Le: exp '<' '=' exp
| Ge: exp '>' '=' exp
| Instof: exp 'instanceof' ty
< Shl: exp '<' '<' exp
| Shr: exp '>' '>' exp
| Ushr: exp '>' '>' '>' exp
< Add: exp '+' exp
| Sub: exp '-' exp
< Mul: exp '*' exp
| Div: exp '/' exp
| Rem: exp '%' exp
> Cast: '(' ty ')' exp
| PreIncr: '++' exp
| PreDecr: '--' exp
| Pos: '+' exp
| Neg: '-' exp
| Not: '!' exp
| Inv: '~' exp
< Offset: exp '[' exp ']'
| Dot: exp '.' exp 
| ExpClass: ty '.' 'class'
| Invoke: exp arg
| PostIncr: exp '++'
| PostDecr: exp '--'
= Inst: targs exp                       // instantiated
= True: 'true'
| False: 'false'
| Null: 'null'
| This: 'this'
| Super: 'super'
| Char: _char
| Long: _int64
| Int: _int32
| Float: _float
| Double: _double
| Str: _string
| Ident: id
| Atom: '(' exp ')'
| NewArrNone: 'new' ty size+ dimen*
| NewArrSome: 'new' ty '{' exps '}'
| NewObj: 'new' name targs? arg bodies?
;

exps:                                  // expression list
> ExpsCons: exp ',' exps
| ExpsSome: exp
| ExpsNil:
;

assign:
= Set: '=' 
| AddSet: '+=' 
| SubSet: '-=' 
| MulSet: '*=' 
| DivSet: '/=' 
| RemSet: '%=' 
| AndSet: '&=' 
| OrSet: '|=' 
| XorSet: '^=' 
| ShlSet: '<' '<' '=' 
| ShrSet: '>' '>' '=' 
| UshrSet: '>' '>' '>' '=' 
;

modifier: #
= AnnotMark: '@' name                   // marker annotation
| AnnotSingle: '@' name '(' exp ')'     // single-element annotation
| AnnotMore: '@' name '(' labelexp ++ ',' ')' // general annotation
| Abstract: 'abstract' 
| Final: 'final' 
| Native: 'native' 
| Private: 'private' 
| Protected: 'protected' 
| Public: 'public'
| Static: 'static' 
| Strictfp: 'strictfp'
| Synchronized: 'synchronized' 
| Transient: 'transient' 
| Volatile: 'volatile' 
;



/* References.

- Official specification:
  http://java.sun.com/docs/books/jls (JLS)
  http://www.lykkenborg.no/java/grammar/JLS3.html
  http://java.sun.com/j2se/1.5.0/docs/guide/language/index.html

- Identifiers vs. keywords: Keywords that occurs _only_ as expressions
can also be specified as identifiers (because identifiers are also
expressions). These include 'true', 'false', 'null', and 'this', but
not 'super'. The keyword 'super' also occurs in the wildcard bound
'WildSuper'. Those tokens ('true', 'false', 'null', and 'this') remain
as keywords here for purely stylistic reason.

- Array initializations, both static and dynamic, can be the empty
array (eg 'int x[] = {}' and 'f(new int[]{})'). Do not use expression
like 'exp ** , ,?' as both the star-closed 'exp' and the optional
marker generate nullable production rules, which results in
exponential behaviour when parsing huge arrays - use 'exps = exp ,
exps | exp | ' instead. (The GLR algorithm 'Right Nulled GLR parsers'
2006 by Elizabeth Scott and Adrian Johnstone may solve this problem.)

- Difference between Java 2 and Java 5 syntax:

-- Generics: generic classes and type parameters (JLS 8.1.2), generic
interfaces and type parameters (JLS 9.1.2), generic methods (JLS
8.4.4), generic constructors (JLS 8.8.4), type arguments and wildcards
(JLS 4.5.1), method invocation expressions (JLS 15.12).

- new 'tparams' and 'tparam', 'targs', modify 'ty' to have 

- add 'targs?' to 'NewArr', 'NewObj', 'NewClass', 'Invoke'

- method call with type instantiation: 'InvokeSome'

- change 'extend', 'extends', and 'implements' to 'ty' (allowing
parameterized types)

- break '>>' and '>>=' (and '<') for token parsing

- 'tparams?' in 'Ctor', 'Method1' and 'Method2'

-- Static import (JLS 7.5): new optional keyword 'static' in 'import'.

-- Annotations (JLS 9): new annotation type declarations 'Annot' (JLS
9.6) and new annotation modifiers 'Annot1', 'Annot2' and 'Annot3' (JLS
9.7).

An annotation type declaration 'Annot' is similar to an interface type
declaration 'Iface', but 'Annot' declaration cannot be generic and do
not have the 'extend' clause. Its method declarations 'Method1' and
'Method2' can have a default value 'default' in the method signature
'signat'.

An annotation expression can either be (1) a marker 'Annot1'
('MarkerAnnotation' in JLS), (2) an application for an single-element
annotation 'Annot2' ('SingleElementAnnotation' in JLS), or (3) a
general annotation 'Annot3' ('NormalAnnotation' in JLS) which is a
list of labelled expression 'labelexp' (zero or more element-value
pairs 'ElementValuePair' in JLS). The scope of the labels in
'labelexp' is implicitly the method names defined by the annotation
type, and hence no qualified identifiers 'name'. Sloppy trailing
commas are _not_ allowed in 'Annot3'.

An annotation expression is a kind of declaration modifier
'modifier'. Since annotations cannot be generic, their denotation is
simply a type name 'name' instead of class with instantiation
'clas'. Since annotation expressions are allowed also in variable
introduction constructs as in (1) an variable declaration statement
'Decl', (2) for-loop statements 'For1' and 'For2', and (3) formal
arguments 'formal' in method declarations, these variable introduction
constructs now takes 'modifier*'. 

-- Enumerations (JLS 8.9): new 'Enum', 'EnumBody', 'enumconst'
('EnumDeclaration', 'EnumBody', 'EnumConstant' in JLS).  Semi-colon
after enumeration constants are optional when there is no class body
declaration, but mandatory when there are declarations afterwards. A
sloppy comma is allowed after enumeration constants.

-- For-each (JLS 14.14.2): new variable of for-loop statement 'For2'
('EnhancedForStatement' in JLS).

-- Varargs (JLS 8.4.1): new 'vararg' in method declaration signature
('LastFormalParameter' in JLS)


One big design decision is where to put '#' (line info for
debugging). An easy choice is to put it everywhere, but it pollutes
the AST too much. In particular, whenever a new type is constructed, a
line info must be constructed too. It becomes very painful in
typechecking. Currently, the line info is only at expressions and
statements. This means that all typechecking functions must pass the
current line info around (in order to have good error messages).

Note: Dot operations are not differentiated syntactically because both names
and expressions are a valid prefix, and an identifier can ambiguously
be either a name or an expression. Only in typing these two forms are
differentiated using the scope of identifiers.

type.class                              // class expression
name.this                               // this (inner class)
void.class                              // class expression
exp.id                                  // field access e.x
super.id                                // field access super.x
name.id                                 // field access n.x
name.super.id                           // field access n.super.x
exp.[targs]id([args])                   // method invocation e.<ts>x(es)
name.[targs]id([args])                  // method invocation n.<ts>x(es)
super.[targs]id([args])                 // method invocation super.<ts>x(es)
name.super.[targs]id([args])            // method invocation n.super.<ts>x(es)
exp.[targs]super([args])                // constructor invocation e.<ts>super(es)
exp.new[targs]id[targs]([args])[body]   // new class e.new<ts>x(ts){body}

name                                    // field access n
name([args])                            // method invocation n(es)
[targs]this([args]);                    // constructor invocation <ts>this(es)
[targs]super([args]);                   // constructor invocation <ts>super(es)

*/


//---- Disambiguation filters.

// If-Else ambiguity: if (0) if (0) 0; else 0;
- stmt: 'If (_, _, If (_,_,_,None), Some _)';

// If-If-Else ambiguity: if (0) if (0) 0; else if (0) 0; else 0;
- stmt: 'If (_, _, If (_,_,_,Some (If (_,_,_,None))), Some _)';

// If-If-If-Else ambiguity: if (0) if (0) 0; else if (0) 0; else if (0) 0; else 0;
- stmt: 'If (_, _, 
If (_,_,_,Some (If (_,_,_, Some (If (_,_,_,None))))), Some _)';


// TODO: We need a recursive filter for dangling-else statements in
// general, but for now, only a finite number are enumerated
// above. The iterative equation is 'if (0) if (0) 0; X else 0;'
// where X='else if (0) 0;' can be repeated many times.

// Cast-Invoke ambiguity: (exp)(exp)
- exp: 'Invoke (_, Atom _, [_])';       // (x)(x);

// Cast-Add ambiguity: (x)+exp, where x is a simple type name
// Cast-Sub ambiguity: (x)-exp, where x is a simple type name
- exp: 'Cast (_, Tname _, Pos _)';      // (x)(x)+x;
- exp: 'Cast (_, Tname _, Neg _)';      // (x)(x)-x;

// Offset-NewArr ambiguity: new int[][]
- exp: 'Offset (_, NewArrNone _, _)';   // new x[x][x];

// Decl-GtLt ambiguity: since greater-than or less-than expressions
// take integers and return boolean, they cannot be nested as 
// '(x1<x2) > x3' or '(x1<x2) > (x=1)', hence the following examples 
// are invalid:
- exp: 'Assign (_, Gt _, _, _)';        // x<x> x = 1;
- exp: 'Assign (_, Lt _, _, _)';        // x<x<x>> x = 1;
- stmt: 'Exp (_, Gt _)';                // x<x> x;
- stmt: 'Exp (_, Lt _)';                // x<x<x>> x;
- stmt: 'ForExp (_, Gt _::_, _, _, _)'; // for (x<x> x;;);
- stmt: 'ForExp (_, Lt _::_, _, _, _)'; // for (x<x<x>> x;;);
