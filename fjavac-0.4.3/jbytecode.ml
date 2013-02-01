(* jbytecode.ml - java classfile bytecode *)

open Std
module T = Jtyped
module A = Jasm
module H = Hashx
module L = Listx


(*

Operations:
- specialize into typed operators (Add -> Iadd, Ladd, Fadd, Dadd)
- minor small value optimizations: Iconst_0, Iload_0
- resolve identifier labels to integer addresses for goto and jump operands

*)

type cfile = {                          (* class file 4.1 *)
  src : string;                         (* source code filename *)
  dst : string;                         (* bytecode class filename *)
  pool : pool;                          (* constant pools *)
  flags : flags;                        (* access flags *)
  this : index;                         (* this class *)
  super : index;                        (* super class *)
  ifaces : index list;                  (* interfaces *)
  fields : finfo list;                  (* fields *)
  methods : minfo list;                 (* methods *)
  attrs : attrs;                        (* attributes *)
}

and ctable = (c, int) H.t
and pool = c array
and finfo = flags * index * index * attrs      (* field info: type, id *)
and minfo = flags * index * index * attrs      (* method info: type, id *)
and flags = A.flags
and label = string                      (* string label *)
and addr = int                          (* code address *)
and index = int                         (* index into constant pool *)

and attr =                              (* attrs 4.7 *)
  | Acode of index * acode                      

and attrs = attr list

(* exception handler *)
and handler = addr * addr * addr * index list

(* max stack, max locals, code, exceptions *)
and acode = int * int * addr ops * handler list (* code attribute 4.7.4 *)


(* For now, double, float, int, long are represented as unparsed string literals. *)
and c =                                 (* constant pool entry *)
  | Cclass of index                     (* 4.4.1 Class_info: name *)
  | Cdouble of float                   (* 4.4.5 Double_info *)
  | Cfield of index * index             (* 4.4.2 Fieldref_info: class, nametype *)
  | Cmethod of index * index            (* 4.4.2 Methodref_info *)
  | Ciface of index * index             (* 4.4.2 InterfaceMethodref_info *)
  | Cstring of index                    (* 4.4.3 String_info: utf8 *)
  | Cint of int32                      (* 4.4.4 Integer_info *)
  | Cfloat of float                    (* 4.4.4 Float_info *)
  | Clong of int64                     (* 4.4.5 Long_info *)
  | Cnametype of index * index          (* 4.4.6 NameAndType_info: name, type *)
  | Cutf8 of string                     (* 4.4.7 Utf8_info *)

and cinfo = string
and metho = string
and name = utf8                         (* qualified name 4.2 *)
and id = utf8                            (* simple name 4.4.6 *)
and utf8 = string                       (* utf-8 4.4.7 *)

and 'l op =                             (* operand with abstract label *)
  | Label of 'l                      (* INTERNAL to jbytecode.ml *)
  | Nop                                 (* 0x00 no operation *)
  | Aconst_null                         (* 0x01 push null reference *)
  | Iconst_m1                           (* 0x02 push int -1 *)
  | Iconst_0                            (* 0x03 push int 0 *)
  | Iconst_1                            (* 0x04 push int 1 *)
  | Iconst_2                            (* 0x05 push int 2 *)
  | Iconst_3                            (* 0x06 push int 3 *)
  | Iconst_4                            (* 0x07 push int 4 *)
  | Iconst_5                            (* 0x08 push int 5 *)
  | Lconst_0                            (* 0x09 push long 0 *)
  | Lconst_1                            (* 0x0a push long 1 *)
  | Fconst_0                            (* 0x0b push float 0 *)
  | Fconst_1                            (* 0x0c push float 1 *)
  | Fconst_2                            (* 0x0d push float 2 *)
  | Dconst_0                            (* 0x0e push double 0 *)
  | Dconst_1                            (* 0x0f push double 1 *)
  | Bipush of int                    (* 0x10 push byte as int *)
  | Sipush of int                    (* 0x11 push short as int *)
  | Ldc of index                         (* 0x12 load from pool *)
  | Ldc_w of index                       (* 0x13 load from pool - wide *)
  | Ldc2_w of index                       (* 0x14 load two from pool - wide *)
  | Iload of index                              (* 0x15 load int variable *)
  | Lload of index                        (* 0x16 load long variable *)
  | Fload of index                        (* 0x17 load float variable *)
  | Dload of index                        (* 0x18 load double variable *)
  | Aload of index                        (* 0x19 load reference variable *)
  | Iload_0                             (* 0x1a load int variable 0 *)
  | Iload_1                             (* 0x1b load int variable 1 *)
  | Iload_2                             (* 0x1c load int variable 2 *)
  | Iload_3                             (* 0x1d load int variable 3 *)
  | Lload_0                             (* 0x1e load long variable 0 *)
  | Lload_1                             (* 0x1f load long variable 1 *)
  | Lload_2                             (* 0x20 load long variable 2 *)
  | Lload_3                             (* 0x21 load long variable 3 *)
  | Fload_0                             (* 0x22 load float variable 0 *)
  | Fload_1                             (* 0x23 load float variable 1 *)
  | Fload_2                             (* 0x24 load float variable 2 *)
  | Fload_3                             (* 0x25 load float variable 3 *)
  | Dload_0                             (* 0x26 load double variable 0 *)
  | Dload_1                             (* 0x27 load double variable 1 *)
  | Dload_2                             (* 0x28 load double variable 2 *)
  | Dload_3                             (* 0x29 load double variable 3 *)
  | Aload_0                             (* 0x2a load reference variable 0 *)
  | Aload_1                             (* 0x2b load reference variable 1 *)
  | Aload_2                             (* 0x2c load reference variable 2 *)
  | Aload_3                             (* 0x2d load reference variable 3 *)
  | Iaload                       (* 0x2e load integer array *)
  | Laload                       (* 0x2f load long array *)
  | Faload                       (* 0x30 load float array *)
  | Daload                       (* 0x31 load double array *)
  | Aaload                       (* 0x32 load reference array *)
  | Baload                       (* 0x33 load byte array *)
  | Caload                       (* 0x34 load char array *)
  | Saload                       (* 0x35 load short array *)
  | Istore of int                       (* 0x36 store int variable *)
  | Lstore of int                       (* 0x37 store long variable *)
  | Fstore of int                       (* 0x38 store float variable *)
  | Dstore of int                       (* 0x39 store double variable *)
  | Astore of int                       (* 0x3a store reference variable *)
  | Istore_0                            (* 0x3b store int variable 0 *)
  | Istore_1                            (* 0x3c store int variable 1 *)
  | Istore_2                            (* 0x3d store int variable 2 *)
  | Istore_3                            (* 0x3e store int variable 3 *)
  | Lstore_0                            (* 0x3f store long variable 0 *)
  | Lstore_1                            (* 0x40 store long variable 1 *)
  | Lstore_2                            (* 0x41 store long variable 2 *)
  | Lstore_3                            (* 0x42 store long variable 3 *)
  | Fstore_0                            (* 0x43 store float variable 0 *)
  | Fstore_1                            (* 0x44 store float variable 1 *)
  | Fstore_2                            (* 0x45 store float variable 2 *)
  | Fstore_3                            (* 0x46 store float variable 3 *)
  | Dstore_0                            (* 0x47 store double variable 0 *)
  | Dstore_1                            (* 0x48 store double variable 1 *)
  | Dstore_2                            (* 0x49 store double variable 2 *)
  | Dstore_3                            (* 0x4a store double variable 3 *)
  | Astore_0                            (* 0x4b store reference variable 0 *)
  | Astore_1                            (* 0x4c store reference variable 1 *)
  | Astore_2                            (* 0x4d store reference variable 2 *)
  | Astore_3                            (* 0x4e store reference variable 3 *)
  | Iastore                      (* 0x4f store integer array *)
  | Lastore                      (* 0x50 store long array *)
  | Fastore                      (* 0x51 store float array *)
  | Dastore                      (* 0x52 store double array *)
  | Aastore                      (* 0x53 store reference array *)
  | Bastore                      (* 0x54 store byte array *)
  | Castore                      (* 0x55 store char array *)
  | Sastore                      (* 0x56 store short array *)
  | Pop                                 (* 0x57 x -> *)
  | Pop2                                (* 0x58 y,x -> *)
  | Dup                                 (* 0x59 x -> x,x *)
  | Dup_x1                              (* 0x5a y,x -> x,y,x *)
  | Dup_x2                              (* 0x5b z,y,x -> x,z,y,x *)
  | Dup2                                (* 0x5c y,x -> y,x,y,x *)
  | Dup2_x1                             (* 0x5d z,y,x -> y,x,z,y,x *)
  | Dup2_x2                             (* 0x5e w,z,y,x -> y,x,w,z,y,x *)
  | Swap                                (* 0x5f y,x -> x,y *)
  | Iadd                                (* 0x60 add int *)
  | Ladd                                (* 0x61 add long *)
  | Fadd                                (* 0x62 add float *)
  | Dadd                                (* 0x63 add double *)
  | Isub                                (* 0x64 subtract int *)
  | Lsub                                (* 0x65 subtract long *)
  | Fsub                                (* 0x66 subtract float *)
  | Dsub                                (* 0x67 subtract double *)
  | Imul                                (* 0x68 multiple int *)
  | Lmul                                (* 0x69 multiple long *)
  | Fmul                                (* 0x6a multiple float *)
  | Dmul                                (* 0x6b multiple double *)
  | Idiv                                (* 0x6c divide int *)
  | Ldiv                                (* 0x6d divide long *)
  | Fdiv                                (* 0x6e divide float *)
  | Ddiv                                (* 0x6f divide double *)
  | Irem                                (* 0x70 remainder int *)
  | Lrem                                (* 0x71 remainder long *)
  | Frem                                (* 0x72 remainder float *)
  | Drem                                (* 0x73 remainder double *)
  | Ineg                                (* 0x74 negate int *)
  | Lneg                                (* 0x75 negate long *)
  | Fneg                                (* 0x76 negate float *)
  | Dneg                                (* 0x77 negate double *)
  | Ishl                                (* 0x78 left-shift int *)
  | Lshl                                (* 0x79 left-shift long *)
  | Ishr                                (* 0x7a right-shift int *)
  | Lshr                                (* 0x7b right-shift long *)
  | Iushr                               (* 0x7c unsigned right-shift int *)
  | Lushr                               (* 0x7d unsigned right-shift long *)
  | Iand                                (* 0x7e bitwise and integer *)
  | Land                                (* 0x7f bitwise and long *)
  | Ior                                 (* 0x80 bitwise or int *)
  | Lor                                 (* 0x81 bitwise or long *)
  | Ixor                                (* 0x82 bitwise xor int *)
  | Lxor                                (* 0x83 bitwise xor long *)
  | Iinc of index * int                   (* 0x84 increment int *)
  | I2l                                 (* 0x85 int to long *)
  | I2f                                 (* 0x86 int to float *)
  | I2d                                 (* 0x87 int to double *)
  | L2i                                 (* 0x88 long to int *)
  | L2f                                 (* 0x89 long to float *)
  | L2d                                 (* 0x8a long to double *)
  | F2i                                 (* 0x8b float to int *)
  | F2l                                 (* 0x8c float to long *)
  | F2d                                 (* 0x8d float to double *)
  | D2i                                 (* 0x8e double to int *)
  | D2l                                 (* 0x8f double to long *)
  | D2f                                 (* 0x90 double to float *)
  | I2b                                 (* 0x91 int to byte *)
  | I2c                                 (* 0x92 int to char *)
  | I2s                                 (* 0x93 int to short *)
  | Lcmp                                (* 0x94 compare long *)
  | Fcmpl                               (* 0x95 compare float with NAN=1 *)
  | Fcmpg                               (* 0x96 compare float with NAN=-1 *)
  | Dcmpl                               (* 0x97 compare double with NAN=1 *)
  | Dcmpg                               (* 0x98 compare double with NAN=-1 *)
  | Ifeq of 'l                                (* 0x99 if = *)
  | Ifne of 'l                                (* 0x9a if <> *)
  | Iflt of 'l                                (* 0x9b if < *)
  | Ifge of 'l                                (* 0x9c if >= *)
  | Ifgt of 'l                                (* 0x9d if > *)
  | Ifle of 'l                                (* 0x9e if <= *)
  | If_icmpeq of 'l                           (* 0x9f if int = *)
  | If_icmpne of 'l                           (* 0xa0 if int <> *)
  | If_icmplt of 'l                           (* 0xa1 if int < *)
  | If_icmpge of 'l                           (* 0xa2 if int >= *)
  | If_icmpgt of 'l                           (* 0xa3 if int > *)
  | If_icmple of 'l                           (* 0xa4 if int <= *)
  | If_acmpeq of 'l                           (* 0xa5 if reference = *)
  | If_acmpne of 'l                           (* 0xa6 if reference <> *)
  | Goto of 'l                               (* 0xa7 goto *)
  | Jsr                                 (* 0xa8 jump subroutine *)
  | Ret                                 (* 0xa9 return from subroutine *)
  | Tableswitch                         (* 0xaa table switch *)
  | Lookupswitch                        (* 0xab lookup switch *)
  | Ireturn                             (* 0xac return int *)
  | Lreturn                             (* 0xad return long *)
  | Freturn                             (* 0xae return float *)
  | Dreturn                             (* 0xaf return double *)
  | Areturn                             (* 0xb0 return reference *)
  | Return                              (* 0xb1 return *)
  | Getstatic of index              (* 0xb2 get static field *)
  | Putstatic of index              (* 0xb3 put static field *)
  | Getfield of index               (* 0xb4 get nonstatic field *)
  | Putfield of index               (* 0xb5 put nonstatic field *)
  | Invokevirtual of index              (* 0xb6 invoke virtual *)
  | Invokespecial of index                      (* 0xb7 invoke special *)
  | Invokestatic of index                        (* 0xb8 invoke static *)
  | Invokeinterface of index                     (* 0xb9 invoke interface *)
  | Unused                              (* 0xba unused *)
  | New of index                        (* 0xbb new *)
  | Newarray of aty                     (* 0xbc new array *)
  | Anewarray of index                  (* 0xbd new reference array *)
  | Arraylength                         (* 0xbe array length *)
  | Athrow                              (* 0xbf throw exception *)
  | Checkcast                           (* 0xc0 check cast *)
  | Instanceof                          (* 0xc1 instance of *)
  | Monitorenter                        (* 0xc2 enter monitor *)
  | Monitorexit                         (* 0xc3 exit monitor *)
  | Wide                                (* 0xc4 widen *)
  | Multianewarray of index * int       (* 0xc5 new multi reference array *)
  | Ifnull                              (* 0xc6 if null *)
  | Ifnonnull                           (* 0xc7 if nonnull *)
  | Goto_w                              (* 0xc8 goto - wide *)
  | Jsr_w                               (* 0xc9 jump subroutine - wide *)
  | Breakpoint                          (* 0xca breakpoint *)
  | Impdep1                             (* 0xfe implementation depedent 1 *)
  | Impdep2                             (* 0xff implementation depedent 2 *)

and 'l ops = 'l op list
and lop = label op                        (* operand with identifier label *)
and aop = addr op                        (* operand with integer label *)

and aty =                               (* array type: JVMS newarray *)
  | Abool
  | Abyte
  | Achar
  | Adouble
  | Afloat
  | Aint
  | Along
  | Ashort

let aty_show : aty -> string = function
  | Abool -> "Z"
  | Abyte -> "B"
  | Achar -> "C"
  | Adouble -> "D"
  | Afloat -> "L"
  | Aint -> "I"
  | Along -> "L"
  | Ashort -> "S"

let op_true = Iconst_1
let op_false = Iconst_0


(*---- Constant pool 'p'. *)

let index (h:ctable) (c:c) : int =
  match H.find h c with
  | None -> let i = H.size h in H.add h c i; i
  | Some i -> i


(*---- Show as string 'show'. *)

let rec c_str (p:pool) : c -> string = function
  | Cint s -> int32_show s
  | Clong s -> int64_show s
  | Cfloat s -> float_show s
  | Cdouble s -> float_show s
  | Cutf8 s -> s
  | Cstring i -> (c_str p p.(i))
  | Cclass i -> (c_str p p.(i))
  | Cfield (i,j) -> (c_str p p.(i)) ^ "." ^ (c_str p p.(j))
  | Ciface (i,j) -> (c_str p p.(i)) ^ "." ^ (c_str p p.(j))
  | Cmethod (i,j) -> (c_str p p.(i)) ^ "." ^ (c_str p p.(j))
  | Cnametype (i,j) -> (c_str p p.(i)) ^ ":" ^ (c_str p p.(j))

and c_show (p:pool) : c -> string = function
  | Cint s -> "int " ^ int32_show s
  | Clong s -> "long " ^ int64_show s
  | Cfloat s -> "float " ^ float_show s
  | Cdouble s -> "double " ^ float_show s
  | Cutf8 s -> "utf8 " ^ s
  | Cstring i -> showf "string %s" (index_show p i)
  | Cclass i -> showf "class %s" (index_show p i)
  | Cfield (i,j) -> 
    showf "field %s %s" (index_show p i) (index_show p j)
  | Ciface (i,j) -> 
    showf "iface %s %s" (index_show p i) (index_show p j)
  | Cmethod (i,j) -> 
    showf "method %s %s" (index_show p i) (index_show p j)
  | Cnametype (i,j) -> 
    showf "nametype %s %s" (index_show p i) (index_show p j)

and index_show (p:pool) (i:index) : string = showf "#%d=%s" i (c_str p p.(i))

and label_show (l:'l) : string = show l (* hack *)
 
and op_show (p:pool) : 'a op -> string = function
  | Label l -> "'l " ^ (label_show l)
  | Nop -> "nop"
  | Aconst_null -> "aconst_null "
  | Iconst_m1 -> "iconst_m1"
  | Iconst_0 -> "iconst_0"
  | Iconst_1 -> "iconst_1"
  | Iconst_2 -> "iconst_2"
  | Iconst_3 -> "iconst_3"
  | Iconst_4 -> "iconst_4"
  | Iconst_5 -> "iconst_5"
  | Lconst_0 -> "lconst_0"
  | Lconst_1 -> "lconst_1"
  | Fconst_0 -> "fconst_0"
  | Fconst_1 -> "fconst_1"
  | Fconst_2 -> "fconst_2"
  | Dconst_0 -> "dconst_0"
  | Dconst_1 -> "dconst_1"
  | Bipush s -> "bipush " ^ (int_show s)
  | Sipush s -> "sipush " ^ (int_show s)
  | Ldc i -> showf "ldc %s" (index_show p i)
  | Ldc_w i -> showf "ldc_w %s" (index_show p i)
  | Ldc2_w i -> showf "ldc2_w %s" (index_show p i)
  | Iload i -> showf "iload %s" (index_show p i)
  | Lload i -> showf "lload %s" (index_show p i)
  | Fload i -> showf "fload %s" (index_show p i)
  | Dload i -> showf "dload %s" (index_show p i)
  | Aload i -> showf "aload %s" (index_show p i)
  | Iload_0 -> "iload_0"
  | Iload_1 -> "iload_1"
  | Iload_2 -> "iload_2"
  | Iload_3 -> "iload_3"
  | Lload_0 -> "lload_0"
  | Lload_1 -> "lload_1"
  | Lload_2 -> "lload_2"
  | Lload_3 -> "lload_3"
  | Fload_0 -> "fload_0"
  | Fload_1 -> "fload_1"
  | Fload_2 -> "fload_2"
  | Fload_3 -> "fload_3"
  | Dload_0 -> "dload_0"
  | Dload_1 -> "dload_1"
  | Dload_2 -> "dload_2"
  | Dload_3 -> "dload_3"
  | Aload_0 -> "aload_0"
  | Aload_1 -> "aload_1"
  | Aload_2 -> "aload_2"
  | Aload_3 -> "aload_3"
  | Iaload -> "iaload"
  | Laload -> "laload"
  | Faload -> "faload"
  | Daload -> "daload"
  | Aaload -> "aaload"
  | Baload -> "baload"
  | Caload -> "caload"
  | Saload -> "saload"
  | Istore i -> showf "istore %d" i
  | Lstore i -> showf "lstore %d" i
  | Fstore i -> showf "fstore %d" i
  | Dstore i -> showf "dstore %d" i
  | Astore i -> showf "astore %d" i
  | Istore_0 -> "istore_0"
  | Istore_1 -> "istore_1"
  | Istore_2 -> "istore_2"
  | Istore_3 -> "istore_3"
  | Lstore_0 -> "lstore_0"
  | Lstore_1 -> "lstore_1"
  | Lstore_2 -> "lstore_2"
  | Lstore_3 -> "lstore_3"
  | Fstore_0 -> "fstore_0"
  | Fstore_1 -> "fstore_1"
  | Fstore_2 -> "fstore_2"
  | Fstore_3 -> "fstore_3"
  | Dstore_0 -> "dstore_0"
  | Dstore_1 -> "dstore_1"
  | Dstore_2 -> "dstore_2"
  | Dstore_3 -> "dstore_3"
  | Astore_0 -> "astore_0"
  | Astore_1 -> "astore_1"
  | Astore_2 -> "astore_2"
  | Astore_3 -> "astore_3"
  | Iastore -> "iastore"
  | Lastore -> "lastore"
  | Fastore -> "fastore"
  | Dastore -> "dastore"
  | Aastore -> "aastore"
  | Bastore -> "bastore"
  | Castore -> "castore"
  | Sastore -> "sastore"
  | Pop -> "pop"
  | Pop2 -> "pop2"
  | Dup -> "dup"
  | Dup_x1 -> "dup_x1"
  | Dup_x2 -> "dup_x2"
  | Dup2 -> "dup2"
  | Dup2_x1 -> "dup2_x1"
  | Dup2_x2 -> "dup2_x2"
  | Swap -> "swap"
  | Iadd -> "iadd"
  | Ladd -> "ladd"
  | Fadd -> "fadd"
  | Dadd -> "dadd"
  | Isub -> "isub"
  | Lsub -> "lsub"
  | Fsub -> "fsub"
  | Dsub -> "dsub"
  | Imul -> "imul "
  | Lmul -> "lmul "
  | Fmul -> "fmul "
  | Dmul -> "dmul "
  | Idiv -> "idiv"
  | Ldiv -> "ldiv"
  | Fdiv -> "fdiv"
  | Ddiv -> "ddiv"
  | Irem -> "irem"
  | Lrem -> "lrem"
  | Frem -> "frem"
  | Drem -> "drem"
  | Ineg -> "ineg"
  | Lneg -> "lneg"
  | Fneg -> "fneg"
  | Dneg -> "dneg"
  | Ishl -> "ishl"
  | Lshl -> "lshl"
  | Ishr -> "ishr"
  | Lshr -> "lshr"
  | Iushr -> "iushr"
  | Lushr -> "lushr"
  | Iand -> "iand"
  | Land -> "land"
  | Ior -> "ior"
  | Lor -> "lor"
  | Ixor -> "ixor"
  | Lxor -> "lxor"
  | Iinc (i,j) -> showf "iinc #%d %d" i j
  | I2l -> "i2l"
  | I2f -> "i2f"
  | I2d -> "i2d"
  | L2i -> "l2i"
  | L2f -> "l2f"
  | L2d -> "l2d"
  | F2i -> "f2i"
  | F2l -> "f2l"
  | F2d -> "f2d"
  | D2i -> "d2i"
  | D2l -> "d2l"
  | D2f -> "d2f"
  | I2b -> "i2b"
  | I2c -> "i2c"
  | I2s -> "i2s"
  | Lcmp -> "lcmp"
  | Fcmpl -> "fcmpl"
  | Fcmpg -> "fcmpg"
  | Dcmpl -> "dcmpl"
  | Dcmpg -> "dcmpg"
  | Ifeq l -> "ifeq " ^ (label_show l)
  | Ifne l -> "ifne " ^ (label_show l)
  | Iflt l -> "iflt " ^ (label_show l)
  | Ifge l -> "ifge " ^ (label_show l)
  | Ifgt l -> "ifgt " ^ (label_show l)
  | Ifle l -> "ifle " ^ (label_show l)
  | If_icmpeq l -> "if_icmpeq " ^ (label_show l)
  | If_icmpne l -> "if_icmpne " ^ (label_show l)
  | If_icmplt l -> "if_icmplt " ^ (label_show l)
  | If_icmpge l -> "if_icmpge " ^ (label_show l)
  | If_icmpgt l -> "if_icmpgt " ^ (label_show l)
  | If_icmple l -> "if_icmple " ^ (label_show l)
  | If_acmpeq l -> "if_acmpeq " ^ (label_show l)
  | If_acmpne l -> "if_acmpne " ^ (label_show l)
  | Goto l -> "goto " ^ (label_show l)
  | Jsr -> "jsr"
  | Ret -> "ret"
  | Tableswitch -> "tableswitch"
  | Lookupswitch -> "lookupswitch"
  | Ireturn -> "ireturn"
  | Lreturn -> "lreturn"
  | Freturn -> "freturn"
  | Dreturn -> "dreturn"
  | Areturn -> "areturn"
  | Return -> "return"
  | Getstatic i -> showf "getstatic %s" (index_show p i)
  | Putstatic i -> showf "putstatic %s" (index_show p i)
  | Getfield i  -> showf "getfield %s" (index_show p i)
  | Putfield i -> showf "putfield %s" (index_show p i)
  | Invokevirtual i -> showf "invokevirtual %s" (index_show p i)
  | Invokespecial i -> showf "invokespecial %s" (index_show p i)
  | Invokestatic i -> showf "invokestatic %s" (index_show p i)
  | Invokeinterface i -> showf "invokeinterface %s" (index_show p i)
  | Unused -> "unused"
  | New i -> showf "new %s" (index_show p i)
  | Newarray a -> "newarray " ^ (aty_show a)
  | Anewarray i -> showf "anewarray %s" (index_show p i)
  | Arraylength -> "arraylength"
  | Athrow -> "athrow"
  | Checkcast -> "checkcast"
  | Instanceof -> "instanceof"
  | Monitorenter -> "monitorenter"
  | Monitorexit -> "monitorexit"
  | Wide -> "wide"
  | Multianewarray (i,j) -> showf "multianewarray #%d %d: %s" i j (index_show p i)
  | Ifnull -> "ifnull"
  | Ifnonnull -> "ifnonnull"
  | Goto_w -> "goto_w"
  | Jsr_w -> "jsr_w"
  | Breakpoint -> "breakpoint"
  | Impdep1 -> "impdep1"
  | Impdep2 -> "impdep2"

and ops_show (p:pool) (os:'a ops) : string = Listx.show1 (op_show p) os

and cfile_show (c:cfile) : string =
  showf "Class file for %s: %s %s extends %s implements [%s]\nPool:\n%s\n\n%s\n%s\n" 
    c.src (A.flags_show c.flags) (index_show c.pool c.this) (index_show c.pool c.super)
    (L.show ", " (index_show c.pool) c.ifaces)
    (pool_show c.pool)
    (L.show1 (finfo_show c.pool) c.fields)
    (L.show1 (minfo_show c.pool) c.methods)

and finfo_show (p:pool) ((fs,t,x,az):finfo) : string =
  showf "Field: %s %s %s\n%s" (A.flags_show fs)
    (index_show p t) (index_show p x) (attrs_show p az)

and minfo_show (p:pool) ((fs,t,x,az):minfo) : string =
  showf "Method: %s %s %s\n%s" (A.flags_show fs)
    (index_show p t) (index_show p x) (attrs_show p az)

and attr_show (p:pool) = function
  | Acode (i, (ns,nx,os,hs)) -> 
    showf "Code attribute %d: max_stack=%d, max_locals=%d,\n%s\n"
      i ns nx (ops_show p os)

and attrs_show (p:pool) (az:attrs) : string = L.show1 (attr_show p) az

and pool_show (p:pool) : string =
  let f i c = showf "#%d: %s" i (c_show p c) in
  Strx.cat1 (Arrayx.to_list (Arrayx.mapi f p))


(*-- 'l resolution. *)

type ltable = (label, addr) H.t            (* 'l table *)

(* size of opcode and its operands *)
let size : 'l op -> int = function
  | Label _ -> 0
  | Nop -> 1
  | Aconst_null -> 1
  | Iconst_m1 -> 1
  | Iconst_0 -> 1
  | Iconst_1 -> 1
  | Iconst_2 -> 1
  | Iconst_3 -> 1
  | Iconst_4 -> 1
  | Iconst_5 -> 1
  | Lconst_0 -> 1
  | Lconst_1 -> 1
  | Fconst_0 -> 1
  | Fconst_1 -> 1
  | Fconst_2 -> 1
  | Dconst_0 -> 1
  | Dconst_1 -> 1
  | Bipush _ -> 2
  | Sipush _ -> 3
  | Ldc _ -> 2
  | Ldc_w _ -> 3
  | Ldc2_w _ -> 3
  | Iload _ -> 2
  | Lload _ -> 2
  | Fload _ -> 2
  | Dload _ -> 2
  | Aload _ -> 2
  | Iload_0 -> 1
  | Iload_1 -> 1
  | Iload_2 -> 1
  | Iload_3 -> 1
  | Lload_0 -> 1
  | Lload_1 -> 1
  | Lload_2 -> 1
  | Lload_3 -> 1
  | Fload_0 -> 1
  | Fload_1 -> 1
  | Fload_2 -> 1
  | Fload_3 -> 1
  | Dload_0 -> 1
  | Dload_1 -> 1
  | Dload_2 -> 1
  | Dload_3 -> 1
  | Aload_0 -> 1
  | Aload_1 -> 1
  | Aload_2 -> 1
  | Aload_3 -> 1
  | Iaload -> 1
  | Laload -> 1
  | Faload -> 1
  | Daload -> 1
  | Aaload -> 1
  | Baload -> 1
  | Caload -> 1
  | Saload -> 1
  | Istore _ -> 2
  | Lstore _ -> 2
  | Fstore _ -> 2
  | Dstore _ -> 2
  | Astore _ -> 2
  | Istore_0 -> 1
  | Istore_1 -> 1
  | Istore_2 -> 1
  | Istore_3 -> 1
  | Lstore_0 -> 1
  | Lstore_1 -> 1
  | Lstore_2 -> 1
  | Lstore_3 -> 1
  | Fstore_0 -> 1
  | Fstore_1 -> 1
  | Fstore_2 -> 1
  | Fstore_3 -> 1
  | Dstore_0 -> 1
  | Dstore_1 -> 1
  | Dstore_2 -> 1
  | Dstore_3 -> 1
  | Astore_0 -> 1
  | Astore_1 -> 1
  | Astore_2 -> 1
  | Astore_3 -> 1
  | Iastore -> 1
  | Lastore -> 1
  | Fastore -> 1
  | Dastore -> 1
  | Aastore -> 1
  | Bastore -> 1
  | Castore -> 1
  | Sastore -> 1
  | Pop -> 1
  | Pop2 -> 1
  | Dup -> 1
  | Dup_x1 -> 1
  | Dup_x2 -> 1
  | Dup2 -> 1
  | Dup2_x1 -> 1
  | Dup2_x2 -> 1
  | Swap -> 1
  | Iadd -> 1
  | Ladd -> 1
  | Fadd -> 1
  | Dadd -> 1
  | Isub -> 1
  | Lsub -> 1
  | Fsub -> 1
  | Dsub -> 1
  | Imul -> 1
  | Lmul -> 1
  | Fmul -> 1
  | Dmul -> 1
  | Idiv -> 1
  | Ldiv -> 1
  | Fdiv -> 1
  | Ddiv -> 1
  | Irem -> 1
  | Lrem -> 1
  | Frem -> 1
  | Drem -> 1
  | Ineg -> 1
  | Lneg -> 1
  | Fneg -> 1
  | Dneg -> 1
  | Ishl -> 1
  | Lshl -> 1
  | Ishr -> 1
  | Lshr -> 1
  | Iushr -> 1
  | Lushr -> 1
  | Iand -> 1
  | Land -> 1
  | Ior -> 1
  | Lor -> 1
  | Ixor -> 1
  | Lxor -> 1
  | Iinc _ -> 3
  | I2l -> 1
  | I2f -> 1
  | I2d -> 1
  | L2i -> 1
  | L2f -> 1
  | L2d -> 1
  | F2i -> 1
  | F2l -> 1
  | F2d -> 1
  | D2i -> 1
  | D2l -> 1
  | D2f -> 1
  | I2b -> 1
  | I2c -> 1
  | I2s -> 1
  | Lcmp -> 1
  | Fcmpl -> 1
  | Fcmpg -> 1
  | Dcmpl -> 1
  | Dcmpg -> 1
  | Ifeq _ -> 3
  | Ifne _ -> 3
  | Iflt _ -> 3
  | Ifge _ -> 3
  | Ifgt _ -> 3
  | Ifle _ -> 3
  | If_icmpeq _ -> 3
  | If_icmpne _ -> 3
  | If_icmplt _ -> 3
  | If_icmpge _ -> 3
  | If_icmpgt _ -> 3
  | If_icmple _ -> 3
  | If_acmpeq _ -> 3
  | If_acmpne _ -> 3
  | Goto _ -> 3
  | Jsr -> 3
  | Ret -> 3
  | Tableswitch -> 23
  | Lookupswitch -> 9
  | Ireturn -> 1
  | Lreturn -> 1
  | Freturn -> 1
  | Dreturn -> 1
  | Areturn -> 1
  | Return -> 1
  | Getstatic _ -> 3
  | Putstatic _ -> 3
  | Getfield _ -> 3
  | Putfield _ -> 3
  | Invokevirtual _ -> 3
  | Invokespecial _ -> 3
  | Invokestatic _ -> 3
  | Invokeinterface _ -> 5
  | Unused -> 1
  | New _ -> 3
  | Newarray _ -> 2
  | Anewarray _ -> 3
  | Arraylength -> 1
  | Athrow -> 1
  | Checkcast -> 3
  | Instanceof -> 3
  | Monitorenter -> 1
  | Monitorexit -> 1
  | Wide -> 1
  | Multianewarray _ -> 4
  | Ifnull -> 3
  | Ifnonnull -> 3
  | Goto_w -> 5
  | Jsr_w -> 5
  | Breakpoint | Impdep1 | Impdep2 -> Std.assert_false () (* unused *)

(* calculate 'l address *)
let op_addr (h:ltable) (i:int) : lop -> unit = function 
  | Label l -> H.add h l i
  | _ -> ()

let rec ops_addr (h:ltable) (i:int) : label ops -> unit = function
  | [] -> ()
  | o::os -> op_addr h i o; ops_addr h (i + size o) os

(* resolve 'l address *)
let label_resolve (h:ltable) (l:'l) : addr =
  try H.get h l
  with Not_found -> error "Jbytecode: 'l not found: %s" l

let op_resolve (h:ltable) : lop -> addr op option = function 
  | Label l -> None
  | Ifeq l -> Some (Ifeq (label_resolve h l))
  | Ifne l -> Some (Ifne (label_resolve h l))
  | Iflt l -> Some (Iflt (label_resolve h l))
  | Ifge l -> Some (Ifge (label_resolve h l))
  | Ifgt l -> Some (Ifgt (label_resolve h l))
  | Ifle l -> Some (Ifle (label_resolve h l))
  | If_icmpeq l -> Some (If_icmpeq (label_resolve h l))
  | If_icmpne l -> Some (If_icmpne (label_resolve h l))
  | If_icmplt l -> Some (If_icmplt (label_resolve h l))
  | If_icmpge l -> Some (If_icmpge (label_resolve h l))
  | If_icmpgt l -> Some (If_icmpgt (label_resolve h l))
  | If_icmple l -> Some (If_icmple (label_resolve h l))
  | If_acmpeq l -> Some (If_acmpeq (label_resolve h l))
  | If_acmpne l -> Some (If_acmpne (label_resolve h l))
  | Goto l -> Some (Goto (label_resolve h l))
  | Nop -> Some (Nop)
  | Aconst_null -> Some (Aconst_null)
  | Iconst_m1 -> Some (Iconst_m1)
  | Iconst_0 -> Some (Iconst_0)
  | Iconst_1 -> Some (Iconst_1)
  | Iconst_2 -> Some (Iconst_2)
  | Iconst_3 -> Some (Iconst_3)
  | Iconst_4 -> Some (Iconst_4)
  | Iconst_5 -> Some (Iconst_5)
  | Lconst_0 -> Some (Lconst_0)
  | Lconst_1 -> Some (Lconst_1)
  | Fconst_0 -> Some (Fconst_0)
  | Fconst_1 -> Some (Fconst_1)
  | Fconst_2 -> Some (Fconst_2)
  | Dconst_0 -> Some (Dconst_0)
  | Dconst_1 -> Some (Dconst_1)
  | Bipush s -> Some (Bipush s)
  | Sipush s -> Some (Sipush s)
  | Ldc i -> Some (Ldc i)
  | Ldc_w i -> Some (Ldc_w i)
  | Ldc2_w i -> Some (Ldc2_w i)
  | Iload i -> Some (Iload i)
  | Lload i -> Some (Lload i)
  | Fload i -> Some (Fload i)
  | Dload i -> Some (Dload i)
  | Aload i -> Some (Aload i)
  | Iload_0 -> Some (Iload_0)
  | Iload_1 -> Some (Iload_1)
  | Iload_2 -> Some (Iload_2)
  | Iload_3 -> Some (Iload_3)
  | Lload_0 -> Some (Lload_0)
  | Lload_1 -> Some (Lload_1)
  | Lload_2 -> Some (Lload_2)
  | Lload_3 -> Some (Lload_3)
  | Fload_0 -> Some (Fload_0)
  | Fload_1 -> Some (Fload_1)
  | Fload_2 -> Some (Fload_2)
  | Fload_3 -> Some (Fload_3)
  | Dload_0 -> Some (Dload_0)
  | Dload_1 -> Some (Dload_1)
  | Dload_2 -> Some (Dload_2)
  | Dload_3 -> Some (Dload_3)
  | Aload_0 -> Some (Aload_0)
  | Aload_1 -> Some (Aload_1)
  | Aload_2 -> Some (Aload_2)
  | Aload_3 -> Some (Aload_3)
  | Iaload -> Some (Iaload)
  | Laload -> Some (Laload)
  | Faload -> Some (Faload)
  | Daload -> Some (Daload)
  | Aaload -> Some (Aaload)
  | Baload -> Some (Baload)
  | Caload -> Some (Caload)
  | Saload -> Some (Saload)
  | Istore i -> Some (Istore i)
  | Lstore i -> Some (Lstore i)
  | Fstore i -> Some (Fstore i)
  | Dstore i -> Some (Dstore i)
  | Astore i -> Some (Astore i)
  | Istore_0 -> Some (Istore_0)
  | Istore_1 -> Some (Istore_1)
  | Istore_2 -> Some (Istore_2)
  | Istore_3 -> Some (Istore_3)
  | Lstore_0 -> Some (Lstore_0)
  | Lstore_1 -> Some (Lstore_1)
  | Lstore_2 -> Some (Lstore_2)
  | Lstore_3 -> Some (Lstore_3)
  | Fstore_0 -> Some (Fstore_0)
  | Fstore_1 -> Some (Fstore_1)
  | Fstore_2 -> Some (Fstore_2)
  | Fstore_3 -> Some (Fstore_3)
  | Dstore_0 -> Some (Dstore_0)
  | Dstore_1 -> Some (Dstore_1)
  | Dstore_2 -> Some (Dstore_2)
  | Dstore_3 -> Some (Dstore_3)
  | Astore_0 -> Some (Astore_0)
  | Astore_1 -> Some (Astore_1)
  | Astore_2 -> Some (Astore_2)
  | Astore_3 -> Some (Astore_3)
  | Iastore -> Some (Iastore)
  | Lastore -> Some (Lastore)
  | Fastore -> Some (Fastore)
  | Dastore -> Some (Dastore)
  | Aastore -> Some (Aastore)
  | Bastore -> Some (Bastore)
  | Castore -> Some (Castore)
  | Sastore -> Some (Sastore)
  | Pop -> Some (Pop)
  | Pop2 -> Some (Pop2)
  | Dup -> Some (Dup)
  | Dup_x1 -> Some (Dup_x1)
  | Dup_x2 -> Some (Dup_x2)
  | Dup2 -> Some (Dup2)
  | Dup2_x1 -> Some (Dup2_x1)
  | Dup2_x2 -> Some (Dup2_x2)
  | Swap -> Some (Swap)
  | Iadd -> Some (Iadd)
  | Ladd -> Some (Ladd)
  | Fadd -> Some (Fadd)
  | Dadd -> Some (Dadd)
  | Isub -> Some (Isub)
  | Lsub -> Some (Lsub)
  | Fsub -> Some (Fsub)
  | Dsub -> Some (Dsub)
  | Imul -> Some (Imul)
  | Lmul -> Some (Lmul)
  | Fmul -> Some (Fmul)
  | Dmul -> Some (Dmul)
  | Idiv -> Some (Idiv)
  | Ldiv -> Some (Ldiv)
  | Fdiv -> Some (Fdiv)
  | Ddiv -> Some (Ddiv)
  | Irem -> Some (Irem)
  | Lrem -> Some (Lrem)
  | Frem -> Some (Frem)
  | Drem -> Some (Drem)
  | Ineg -> Some (Ineg)
  | Lneg -> Some (Lneg)
  | Fneg -> Some (Fneg)
  | Dneg -> Some (Dneg)
  | Ishl -> Some (Ishl)
  | Lshl -> Some (Lshl)
  | Ishr -> Some (Ishr)
  | Lshr -> Some (Lshr)
  | Iushr -> Some (Iushr)
  | Lushr -> Some (Lushr)
  | Iand -> Some (Iand)
  | Land -> Some (Land)
  | Ior -> Some (Ior)
  | Lor -> Some (Lor)
  | Ixor -> Some (Ixor)
  | Lxor -> Some (Lxor)
  | Iinc (i,j) -> Some (Iinc (i,j))
  | I2l -> Some (I2l)
  | I2f -> Some (I2f)
  | I2d -> Some (I2d)
  | L2i -> Some (L2i)
  | L2f -> Some (L2f)
  | L2d -> Some (L2d)
  | F2i -> Some (F2i)
  | F2l -> Some (F2l)
  | F2d -> Some (F2d)
  | D2i -> Some (D2i)
  | D2l -> Some (D2l)
  | D2f -> Some (D2f)
  | I2b -> Some (I2b)
  | I2c -> Some (I2c)
  | I2s -> Some (I2s)
  | Lcmp -> Some (Lcmp)
  | Fcmpl -> Some (Fcmpl)
  | Fcmpg -> Some (Fcmpg)
  | Dcmpl -> Some (Dcmpl)
  | Dcmpg -> Some (Dcmpg)
  | Jsr -> Some (Jsr)
  | Ret -> Some (Ret)
  | Tableswitch -> Some (Tableswitch)
  | Lookupswitch -> Some (Lookupswitch)
  | Ireturn -> Some (Ireturn)
  | Lreturn -> Some (Lreturn)
  | Freturn -> Some (Freturn)
  | Dreturn -> Some (Dreturn)
  | Areturn -> Some (Areturn)
  | Return -> Some (Return)
  | Getstatic i -> Some (Getstatic i)
  | Putstatic i -> Some (Putstatic i)
  | Getfield i  -> Some (Getfield i)
  | Putfield i -> Some (Putfield i)
  | Invokevirtual i -> Some (Invokevirtual i)
  | Invokespecial i -> Some (Invokespecial i)
  | Invokestatic i -> Some (Invokestatic i)
  | Invokeinterface i -> Some (Invokeinterface i)
  | Unused -> Some (Unused)
  | New i -> Some (New i)
  | Newarray a -> Some (Newarray a)
  | Anewarray i -> Some (Anewarray i)
  | Arraylength -> Some (Arraylength)
  | Athrow -> Some (Athrow)
  | Checkcast -> Some (Checkcast)
  | Instanceof -> Some (Instanceof)
  | Monitorenter -> Some (Monitorenter)
  | Monitorexit -> Some (Monitorexit)
  | Wide -> Some (Wide)
  | Multianewarray (i,j) -> Some (Multianewarray (i,j))
  | Ifnull -> Some (Ifnull)
  | Ifnonnull -> Some (Ifnonnull)
  | Goto_w -> Some (Goto_w)
  | Jsr_w -> Some (Jsr_w)
  | Breakpoint -> Some (Breakpoint)
  | Impdep1 -> Some (Impdep1)
  | Impdep2 -> Some (Impdep2)


let ops_resolve (os:label ops) : addr ops = 
  let h = H.make 2 in
  ops_addr h 0 os;
  Listx.collect (op_resolve h) os


(*---- Translation 'of'. 

Note: 'h' is a hash table for the constant pool and 'h' is updated
imperatively.

*)

(*-- Integer promotion for boolean, char, short, and byte. *)

let ty_int : A.ty -> A.ty = function
  | A.Tbool | A.Tbyte | A.Tchar | A.Tshort -> A.Tint
  | t -> t

let op_int : A.op -> A.op = function
  | A.Load (t,i) -> A.Load (ty_int t, i)
  | A.Store (t,i) -> A.Store (ty_int t, i)
  | A.Aload t -> A.Aload (ty_int t)
  | A.Astore t -> A.Astore (ty_int t)
  | A.Add t -> A.Add (ty_int t)
  | A.Sub t -> A.Sub (ty_int t)
  | A.Mul t -> A.Mul (ty_int t)
  | A.Div t -> A.Div (ty_int t)
  | A.Rem t -> A.Rem (ty_int t)
  | A.Neg t -> A.Neg (ty_int t)
  | A.Shl t -> A.Shl (ty_int t)
  | A.Shr t -> A.Shr (ty_int t)
  | A.Ushr t -> A.Ushr (ty_int t)
  | A.And t -> A.And (ty_int t)
  | A.Or t -> A.Or (ty_int t)
  | A.Xor t -> A.Xor (ty_int t)
  | A.Inc (t,i,j) -> A.Inc (ty_int t, i, j)
  | A.Cmp (t,c) -> A.Cmp (ty_int t, c)
  | A.Return tp -> A.Return (Std.opt_map ty_int tp)
  | A.New (A.Tarray t) -> A.New (A.Tarray (ty_int t))
  | o -> o

let rec op_of (h:ctable) : A.op -> label ops = function
  | A.Nop -> [Nop]
  | A.Char s -> 
    if (String.length s > 1) then warn "FIXME: unicode unsupported";
    let i = Char.code (String.get s 0) in
    [Bipush i]              (* use Sipush for large char *)
  | A.Int 0l -> [Iconst_0]             (* TODO: other small constants *)
  | A.Int s -> [Bipush (int32_to s)]               (* use Sipush for large int *)
  | A.Long s -> [Ldc2_w (index h (Clong s))]
  | A.Float s -> [Ldc (index h (Cfloat s))]
  | A.Double s -> [Ldc2_w (index h (Cdouble s))]
  | A.Str s -> [Ldc (index h (Cstring (index h (Cutf8 s))))]
  | A.Class s -> [Ldc2_w (index h (Cclass (index h (Cutf8 s))))]
  | A.Null -> [Aconst_null]
  | A.Load (A.Tint,0) -> [Iload_0]
  | A.Load (A.Tint,1) -> [Iload_1]
  | A.Load (A.Tint,2) -> [Iload_2]
  | A.Load (A.Tint,3) -> [Iload_3]
  | A.Load (A.Tint,i) -> [Iload i]
  | A.Load (A.Tlong,0) -> [Lload_0]
  | A.Load (A.Tlong,1) -> [Lload_1]
  | A.Load (A.Tlong,2) -> [Lload_2]
  | A.Load (A.Tlong,3) -> [Lload_3]
  | A.Load (A.Tlong,i) -> [Lload i]
  | A.Load (A.Tfloat,0) -> [Fload_0]
  | A.Load (A.Tfloat,1) -> [Fload_1]
  | A.Load (A.Tfloat,2) -> [Fload_2]
  | A.Load (A.Tfloat,3) -> [Fload_3]
  | A.Load (A.Tfloat,i) -> [Fload i]
  | A.Load (A.Tdouble,0) -> [Dload_0]
  | A.Load (A.Tdouble,1) -> [Dload_1]
  | A.Load (A.Tdouble,2) -> [Dload_2]
  | A.Load (A.Tdouble,3) -> [Dload_3]
  | A.Load (A.Tdouble,i) -> [Dload i]
  | A.Load (A.Tref _,0) | A.Load (A.Tarray _,0) -> [Aload_0]
  | A.Load (A.Tref _,1) | A.Load (A.Tarray _,1) -> [Aload_1]
  | A.Load (A.Tref _,2) | A.Load (A.Tarray _,2) -> [Aload_2]
  | A.Load (A.Tref _,3) | A.Load (A.Tarray _,3) -> [Aload_3]
  | A.Load (A.Tref _,i) | A.Load (A.Tarray _,i) -> [Aload i]
  | A.Aload A.Tbyte -> [Iaload]
  | A.Aload A.Tbool -> [Iaload]
  | A.Aload A.Tchar -> [Iaload]
  | A.Aload A.Tint -> [Iaload]
  | A.Aload A.Tshort -> [Iaload]
  | A.Aload A.Tlong -> [Laload]
  | A.Aload A.Tfloat -> [Faload]
  | A.Aload A.Tdouble -> [Daload]
  | A.Aload (A.Tref _) | A.Aload (A.Tarray _) -> [Aaload]
  | A.Store (A.Tint,0) -> [Istore_0]
  | A.Store (A.Tint,1) -> [Istore_1]
  | A.Store (A.Tint,2) -> [Istore_2]
  | A.Store (A.Tint,3) -> [Istore_3]
  | A.Store (A.Tint,i) -> [Istore i]
  | A.Store (A.Tlong,0) -> [Lstore_0]
  | A.Store (A.Tlong,1) -> [Lstore_1]
  | A.Store (A.Tlong,2) -> [Lstore_2]
  | A.Store (A.Tlong,3) -> [Lstore_3]
  | A.Store (A.Tlong,i) -> [Lstore i]
  | A.Store (A.Tfloat,0) -> [Fstore_0]
  | A.Store (A.Tfloat,1) -> [Fstore_1]
  | A.Store (A.Tfloat,2) -> [Fstore_2]
  | A.Store (A.Tfloat,3) -> [Fstore_3]
  | A.Store (A.Tfloat,i) -> [Fstore i]
  | A.Store (A.Tdouble,0) -> [Dstore_0]
  | A.Store (A.Tdouble,1) -> [Dstore_1]
  | A.Store (A.Tdouble,2) -> [Dstore_2]
  | A.Store (A.Tdouble,3) -> [Dstore_3]
  | A.Store (A.Tdouble,i) -> [Dstore i]
  | A.Store (A.Tref _,0) | A.Store (A.Tarray _,0) -> [Astore_0]
  | A.Store (A.Tref _,1) | A.Store (A.Tarray _,1) -> [Astore_1]
  | A.Store (A.Tref _,2) | A.Store (A.Tarray _,2) -> [Astore_2]
  | A.Store (A.Tref _,3) | A.Store (A.Tarray _,3) -> [Astore_3]
  | A.Store (A.Tref _,i) | A.Store (A.Tarray _,i) -> [Astore i]
  | A.Astore A.Tint -> [Iastore]
  | A.Astore A.Tlong -> [Lastore]
  | A.Astore A.Tfloat -> [Fastore]
  | A.Astore A.Tdouble -> [Dastore]
  | A.Astore (A.Tref _) | A.Astore (A.Tarray _) -> [Aastore]
  | A.Dup (1,0) -> [Dup]
  | A.Dup (1,1) -> [Dup_x1]
  | A.Dup (1,2) -> [Dup_x2]
  | A.Dup (2,0) -> [Dup2]
  | A.Dup (2,1) -> [Dup2_x1]
  | A.Dup (2,2) -> [Dup2_x2]
  | A.Pop 0 -> []
  | A.Pop 1 -> [Pop]
  | A.Pop 2 -> [Pop2]
  | A.Pop i when i > 2 -> Pop2 :: op_of h (A.Pop (i-2))
  | A.Swap -> [Swap]
  | A.Add A.Tint -> [Iadd]
  | A.Add A.Tlong -> [Ladd]
  | A.Add A.Tfloat -> [Fadd]
  | A.Add A.Tdouble -> [Dadd]
  | A.Add _ -> []                       (* FIXME: add string *)
  | A.Sub A.Tint -> [Isub]
  | A.Sub A.Tlong -> [Lsub]
  | A.Sub A.Tfloat -> [Fsub]
  | A.Sub A.Tdouble -> [Dsub]
  | A.Mul A.Tint -> [Imul]
  | A.Mul A.Tlong -> [Lmul]
  | A.Mul A.Tfloat -> [Fmul]
  | A.Mul A.Tdouble -> [Dmul]
  | A.Div A.Tint -> [Idiv]
  | A.Div A.Tlong -> [Ldiv]
  | A.Div A.Tfloat -> [Fdiv]
  | A.Div A.Tdouble -> [Ddiv]
  | A.Rem A.Tint -> [Irem]
  | A.Rem A.Tlong -> [Lrem]
  | A.Rem A.Tfloat -> [Frem]
  | A.Rem A.Tdouble -> [Drem]
  | A.Neg A.Tint -> [Ineg]
  | A.Neg A.Tlong -> [Lneg]
  | A.Neg A.Tfloat -> [Fneg]
  | A.Neg A.Tdouble -> [Dneg]
  | A.Shl A.Tint -> [Ishl]
  | A.Shl A.Tlong -> [Lshl]
  | A.Shr A.Tint -> [Ishr]
  | A.Shr A.Tlong -> [Lshr]
  | A.Ushr A.Tint -> [Iushr]
  | A.Ushr A.Tlong -> [Lushr]
  | A.And A.Tint -> [Iand]
  | A.And A.Tlong -> [Land]
  | A.Or A.Tint -> [Ior]
  | A.Or A.Tlong -> [Lor]
  | A.Xor A.Tint -> [Ixor]
  | A.Xor A.Tlong -> [Lxor]
  | A.Inc (A.Tint,i,j) -> [Iinc (i,j)]  (* TODO check range of increment *)
  | A.Cmp (t,c) -> cmp_of t c
  | A.Conv (A.Tint,A.Tlong) -> [I2l]
  | A.Conv (A.Tint,A.Tfloat) -> [I2f]
  | A.Conv (A.Tint,A.Tdouble) -> [I2d]
  | A.Conv (A.Tlong,A.Tint) -> [L2i]
  | A.Conv (A.Tlong,A.Tfloat) -> [L2f]
  | A.Conv (A.Tlong,A.Tdouble) -> [L2d]
  | A.Conv (A.Tfloat,A.Tint) -> [F2i]
  | A.Conv (A.Tfloat,A.Tlong) -> [F2l]
  | A.Conv (A.Tfloat,A.Tdouble) -> [F2d]
  | A.Conv (A.Tdouble,A.Tint) -> [D2i]
  | A.Conv (A.Tdouble,A.Tlong) -> [D2l]
  | A.Conv (A.Tdouble,A.Tfloat) -> [D2f]
  | A.Conv (A.Tint,A.Tbyte) -> [I2b]
  | A.Conv (A.Tint,A.Tchar) -> [I2c]
  | A.Conv (A.Tint,A.Tshort) -> [I2s]
  | A.Conv _ -> []                      (* FIXME: remove upcast from jtyped.ml *)
  | A.Ifeq l -> [Ifeq l]
  | A.Ifne l -> [Ifne l]
  | A.Goto l -> [Goto l]
  | A.Label l -> [Label l]
  | A.Jsr -> [Jsr]
  | A.Ret -> [Ret]
  | A.Switch -> [Tableswitch]
  | A.Return (Some A.Tbool) -> [Ireturn]
  | A.Return (Some A.Tbyte) -> [Ireturn]
  | A.Return (Some A.Tchar) -> [Ireturn]
  | A.Return (Some A.Tint) -> [Ireturn]
  | A.Return (Some A.Tlong) -> [Lreturn]
  | A.Return (Some A.Tfloat) -> [Freturn]
  | A.Return (Some A.Tdouble) -> [Dreturn]
  | A.Return (Some (A.Tref _)) -> [Areturn]
  | A.Return (Some (A.Tarray _)) -> [Areturn]
  | A.Return None -> [Return]
  | A.Get ((fs,_,_,_) as t) when A.is_static fs -> [Getstatic (fty_of h t)]
  | A.Get ((fs,_,_,_) as t) -> [Getfield (fty_of h t)]
  | A.Put ((fs,_,_,_) as t) when A.is_static fs -> [Putstatic (fty_of h t)]
  | A.Put ((fs,_,_,_) as t) -> [Putfield (fty_of h t)]
  | A.Invoke ((_,k,_,_,_,_) as m) -> invoke_of (mty_of h m) k
  | A.New (A.Tarray A.Tbool) -> [Newarray Abool]
  | A.New (A.Tarray A.Tbyte) -> [Newarray Abyte]
  | A.New (A.Tarray A.Tchar) -> [Newarray Achar]
  | A.New (A.Tarray A.Tdouble) -> [Newarray Adouble]
  | A.New (A.Tarray A.Tfloat) -> [Newarray Afloat]
  | A.New (A.Tarray A.Tint) -> [Newarray Aint]
  | A.New (A.Tarray A.Tlong) -> [Newarray Along]
  | A.New (A.Tarray A.Tshort) -> [Newarray Ashort]
  | A.New ((A.Tarray _) as t) ->               (* use multianewarray *)
    [Anewarray (index h (Cclass (index h (Cutf8 (A.ty_show t)))))]
  | A.New (A.Tref c) -> [New (class_of h c)]
  | A.Arraylength -> [Arraylength]
  | A.Athrow -> [Athrow]
  | A.Instanceof _ -> [Instanceof]
  | A.Monitorenter -> [Monitorenter]
  | A.Monitorexit -> [Monitorexit]
  | _ as o -> error "Jbytecodem: invalid opcode: %s" (A.op_show o)

and cname_of (h:ctable) (c:A.cname) : int = index h (Cutf8 (A.cname_show c))

and class_of (h:ctable) (c:A.cname) : int = index h (Cclass (cname_of h c))

and cmp_of (t:A.ty) (c:A.cmp) : label ops =
  let ltrue = A.new_label "true-jcfile.ml" in
  let lend = A.new_label "end-jcfile.ml" in
  let os = [op_false; Goto lend; Label ltrue; op_true; Label lend] in
  match (t,c) with
  | (A.Tint,_) -> if_int_of ltrue c :: os
  | (A.Tlong,_) -> Lcmp :: if_of ltrue c :: os
  | (A.Tfloat,_) -> Fcmpl :: if_of ltrue c :: os
  | (A.Tdouble,_) -> Dcmpl :: if_of ltrue c :: os
  | (A.Tref _,A.Eq) -> If_acmpeq ltrue :: os
  | (A.Tref _,A.Ne) -> If_acmpne ltrue :: os
  | (A.Tarray _,A.Eq) -> If_acmpeq ltrue :: os
  | (A.Tarray _,A.Ne) -> If_acmpne ltrue :: os
  | _ -> printf "invalid comparison: %s, %s\n" 
      (A.ty_show t) (A.cmp_show c); Std.assert_false ()

and if_of (l:'l) : A.cmp -> lop = function
  | A.Eq -> Ifeq l
  | A.Ne -> Ifne l
  | A.Lt -> Iflt l
  | A.Ge -> Ifge l
  | A.Gt -> Ifgt l
  | A.Le -> Ifle l

and if_int_of (l:'l) : A.cmp -> lop = function
  | A.Eq -> If_icmpeq l
  | A.Ne -> If_icmpne l
  | A.Lt -> If_icmplt l
  | A.Ge -> If_icmpge l
  | A.Gt -> If_icmpgt l
  | A.Le -> If_icmple l

and invoke_of (i:index) : T.ikind -> label ops = function
  | T.Iiface -> [Invokeinterface i]
  | T.Ispecial -> [Invokespecial i]
  | T.Ivirtual -> [Invokevirtual i]
  | T.Istatic -> [Invokestatic i]

and mty_of (h:ctable) ((_,_,t,c,x,ts):A.mty) : index =
  let s = showf "(%s)%s" (Listx.show0 A.ty_show ts) (A.ty_show t) in
  let ti = index h (Cutf8 s) in
  let ni = cname_of h c in
  let xi = index h (Cutf8 x) in
  let nti = index h (Cnametype (xi, ti)) in
  let ci = index h (Cclass ni) in
  index h (Cmethod (ci, nti))
  
and fty_of (h:ctable) ((_,t,c,x):A.fty) : index =
  let ti = index h (Cutf8 (A.ty_show t)) in
  let ni = cname_of h c in
  let xi = index h (Cutf8 x) in
  let nti = index h (Cnametype (xi, ti)) in
  let ci = index h (Cclass ni) in
  index h (Cfield (ci, nti))

and ctask_of (cs:A.cfile list) : cfile list = L.map cunit_of cs 

and cunit_of (c:A.cfile) : cfile = 
  let h = H.make 2 in
  let c2 = {
    src = c.A.src;
    dst = get3 c.A.this ^ ".class";
    pool = [||];                        (* to be updated imperatively *)
    flags = c.A.flags;
    this = class_of h c.A.this;
    super = class_of h c.A.super;
    ifaces = L.map (class_of h) c.A.ifaces;
    fields = L.map (finfo_of h) c.A.fields;
    methods = L.map (minfo_of h) c.A.methods;
    attrs = [];
  } in
  { c2 with pool = H.to_index_array h }

and attr_of (h:ctable) : A.attr -> attr = function
  | A.Acode (ns,nx,os,hs) ->
    let i = index h (Cutf8 "Code") in
    let os2 = Listx.mapc (fun o -> op_of h (op_int o)) os in
    Acode (i, (ns, nx, ops_resolve os2, []))

and attrs_of (h:ctable) (az:A.attrs) : attrs = L.map (attr_of h) az

and finfo_of (h:ctable) (((fs,t,_,x),a):A.finfo) : finfo =
  let i = index h (Cutf8 (A.ty_show t)) in
  (fs, i, index h (Cutf8 x), attrs_of h a)

and minfo_of (h:ctable) (((fs,_,t,_,x,ts),a):A.minfo) : minfo = 
  let s = showf "(%s)%s" (Listx.show0 A.ty_show ts) (A.ty_show t) in 
  (fs, index h (Cutf8 s), index h (Cutf8 x), attrs_of h a)
