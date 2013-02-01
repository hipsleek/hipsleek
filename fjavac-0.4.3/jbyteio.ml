(* jbyteio.ml - java classfile bytecode I/O *)
(* written by Dan Margolis <dmargoli@seas.upenn.edu> *)

module A = Jasm
open Jbytecode

let debug_string (s:string) : unit = 
  if Util.arg_bool "-d" then Std.printl s

(** Write a single byte to an out channel *)
let instr8 (f:out_channel) (b:int) : unit = 
  let byte = b mod 256 in 
  output_byte f byte

(** Write two bytes to an out channel *)
let instr16 (f:out_channel) (b:int) : unit = 
  instr8 f (b lsr 8); instr8 f b

(** Write four bytes to an out channel *)
let instr32 (f:out_channel) (b:int32) : unit = 
  instr16 f (Int32.to_int (Int32.shift_right b 16));
  instr16 f (Int32.to_int b)

(** Write eight bytes to an out channel *)
let instr64 (f:out_channel) (b:int64) : unit = 
  instr32 f (Int64.to_int32 (Int64.shift_right b 32));
  instr32 f (Int64.to_int32 b)

(** Write the magic number to the class file *)
let write_magic (f:out_channel) : unit = 
  instr32 f 0xCAFEBABEl

(** Write the minor and major version *)
let write_versions (f:out_channel) : unit = 
  instr16 f 0x0000;
  instr16 f 0x0031

(** Write the Constant Pool *)
let write_cpool (f:out_channel) (cpool:pool) : unit = 
  let write_constant (c:c) : unit = 
    match c with 
      | Cclass i -> instr8 f 7; instr16 f (i + 1); debug_string "cclass"
      | Cdouble s -> instr8 f 6; 
                     instr64 f (Int64.bits_of_float s); 
                     (*instr32 f (Int32.shift_left (float_to_bytes s) 4);*) debug_string "cdouble"
      | Cfield (i1, i2) -> instr8 f 9; instr16 f (i1 + 1); instr16 f (i2 + 1); debug_string "cfield"
      | Cmethod (i1, i2) -> instr8 f 10; instr16 f (i1 + 1); instr16 f (i2 + 1); debug_string "cmethod"
      | Ciface (i1, i2) -> instr8 f 11; instr16 f (i1 + 1); instr16 f (i2 + 1); debug_string "ciface"
      | Cstring i -> instr8 f 8; instr16 f (i + 1); debug_string "cstring"
      | Cint s -> instr8 f 3; instr32 f s; debug_string "cint"
      | Cfloat s -> instr8 f 7; instr32 f (Int32.bits_of_float s); debug_string "cfloat"
      | Clong s -> instr8 f 5; instr64 f s (*(int64_to_int s)*);  
                   (*instr32 f (Int32.shift_left (int64_to_int s) 4);*) debug_string "clong"
      | Cnametype (i1, i2) -> instr8 f 12; instr16 f (i1 + 1); instr16 f (i2 + 1); debug_string (Printf.sprintf "cnametype %d %d" i1 i2)
      | Cutf8 s -> instr8 f 1; instr16 f (String.length s);
                   String.iter (fun x -> instr8 f (int_of_char x)) s; debug_string ( Printf.sprintf "cutf8 %s" s)
  in (* write cpool count *)
    debug_string "Starting cpool";
    debug_string (Printf.sprintf "Cpool len: %d" (Array.length cpool));
    instr16 f ((Array.length cpool) + 1); 
    Array.iter write_constant cpool
      
let rec get_class_hack cur index c = 
  match c.pool.(cur) with 
      Cclass i -> if i = index then cur
      else get_class_hack (cur + 1) index c
    | _ -> get_class_hack (cur + 1) index c

(** Write the this_class index *)
let write_thisclass (f:out_channel) (c:cfile) : unit = 
  instr16 f (c.this + 1)

(** Write the super_class index *)
let write_superclass (f:out_channel) (c:cfile) : unit = 
  instr16 f (c.super + 1)

(** Write the interfaces *)
let write_interfaces (f:out_channel) (c:cfile) : unit = 
  instr16 f (List.length(c.ifaces));
  List.iter (fun x -> instr16 f x) c.ifaces  

(** Write a single opcode to the given output channel *)
let write_opcode (f:out_channel) (op:aop) : unit = 
  match op with 
    | Label i -> Std.assert_false ()
    | Nop -> instr8 f 0x00 
    | Aconst_null -> instr8 f 0x01
    | Iconst_m1 -> instr8 f 0x02 
    | Iconst_0 -> instr8 f 0x03
    | Iconst_1 -> instr8 f 0x04
    | Iconst_2 -> instr8 f 0x05
    | Iconst_3 -> instr8 f 0x06
    | Iconst_4 -> instr8 f 0x07
    | Iconst_5 -> instr8 f 0x08
    | Lconst_0 -> instr8 f 0x09
    | Lconst_1 -> instr8 f 0x0a
    | Fconst_0 -> instr8 f 0x0b
    | Fconst_1 -> instr8 f 0x0c
    | Fconst_2 -> instr8 f 0x0d 
    | Dconst_0 -> instr8 f 0x0e 
    | Dconst_1 -> instr8 f 0x0f
    | Bipush x -> instr8 f 0x10; instr8 f x
    | Sipush x -> instr8 f 0x11; instr16 f x
    | Ldc ind -> instr8 f 0x12; instr8 f (ind + 1) 
    | Ldc_w ind -> instr8 f 0x13; instr16 f (ind + 1) 
    | Ldc2_w ind -> instr8 f 0x14; instr16 f (ind + 1) 
    | Iload i -> instr8 f 0x15; instr8 f i  (* float_to_bytes: should this be 1 indexed? *)
    | Lload i -> instr8 f 0x16; instr8 f i (* float_to_bytes: same as above?*)
    | Fload i -> instr8 f 0x16; instr8 f i (* float_to_bytes: same as above? *)
    | Dload i -> instr8 f 0x18; instr8 f i (* float_to_bytes: same as above? *)
    | Aload i -> instr8 f 0x19;         
    | Iload_0 -> instr8 f 0x1a         
    | Iload_1 -> instr8 f 0x1b 
    | Iload_2 -> instr8 f 0x1c
    | Iload_3 -> instr8 f 0x1d
    | Lload_0 -> instr8 f 0x1e
    | Lload_1 -> instr8 f 0x1f
    | Lload_2 -> instr8 f 0x20
    | Lload_3 -> instr8 f 0x21
    | Fload_0 -> instr8 f 0x22
    | Fload_1 -> instr8 f 0x23
    | Fload_2 -> instr8 f 0x24
    | Fload_3 -> instr8 f 0x25
    | Dload_0 -> instr8 f 0x26
    | Dload_1 -> instr8 f 0x27
    | Dload_2 -> instr8 f 0x28
    | Dload_3 -> instr8 f 0x29
    | Aload_0 -> instr8 f 0x2a
    | Aload_1 -> instr8 f 0x2b
    | Aload_2 -> instr8 f 0x2c
    | Aload_3 -> instr8 f 0x2d
    | Iaload -> instr8 f 0x2e
    | Laload -> instr8 f 0x2f
    | Faload -> instr8 f 0x30
    | Daload -> instr8 f 0x31
    | Aaload -> instr8 f 0x32
    | Baload -> instr8 f 0x33
    | Caload -> instr8 f 0x34
    | Saload -> instr8 f 0x35
    | Istore i -> instr8 f 0x36; instr8 f i 
    | Lstore i -> instr8 f 0x37; instr8 f i
    | Fstore i -> instr8 f 0x38; instr8 f i
    | Dstore i -> instr8 f 0x39; instr8 f i
    | Astore i -> instr8 f 0x3a; instr8 f i
    | Istore_0 -> instr8 f 0x3b
    | Istore_1 -> instr8 f 0x3c
    | Istore_2 -> instr8 f 0x3d 
    | Istore_3 -> instr8 f 0x3e 
    | Lstore_0 -> instr8 f 0x3f 
    | Lstore_1 -> instr8 f 0x40 
    | Lstore_2 -> instr8 f 0x41 
    | Lstore_3 -> instr8 f 0x42 
    | Fstore_0 -> instr8 f 0x43 
    | Fstore_1 -> instr8 f 0x44 
    | Fstore_2 -> instr8 f 0x45 
    | Fstore_3 -> instr8 f 0x46 
    | Dstore_0 -> instr8 f 0x47 
    | Dstore_1 -> instr8 f 0x48 
    | Dstore_2 -> instr8 f 0x49 
    | Dstore_3 -> instr8 f 0x4a 
    | Astore_0 -> instr8 f 0x4b 
    | Astore_1 -> instr8 f 0x4c 
    | Astore_2 -> instr8 f 0x4d 
    | Astore_3 -> instr8 f 0x4e 
    | Iastore -> instr8 f 0x4f
    | Lastore -> instr8 f 0x50
    | Fastore -> instr8 f 0x51
    | Dastore -> instr8 f 0x52
    | Aastore -> instr8 f 0x53
    | Bastore -> instr8 f 0x54
    | Castore -> instr8 f 0x55
    | Sastore -> instr8 f 0x56
    | Pop -> instr8 f 0x57
    | Pop2 -> instr8 f 0x58
    | Dup -> instr8 f 0x59
    | Dup_x1 -> instr8 f 0x5a
    | Dup_x2 -> instr8 f 0x5b
    | Dup2 -> instr8 f 0x5c
    | Dup2_x1 -> instr8 f 0x5d
    | Dup2_x2 -> instr8 f 0x5e
    | Swap -> instr8 f 0x5f
    | Iadd -> instr8 f 0x60
    | Ladd -> instr8 f 0x61
    | Fadd -> instr8 f 0x62
    | Dadd -> instr8 f 0x63
    | Isub -> instr8 f 0x64
    | Lsub -> instr8 f 0x65
    | Fsub -> instr8 f 0x66
    | Dsub -> instr8 f 0x67
    | Imul -> instr8 f 0x68
    | Lmul -> instr8 f 0x69
    | Fmul -> instr8 f 0x6a
    | Dmul -> instr8 f 0x6b
    | Idiv -> instr8 f 0x6c
    | Ldiv -> instr8 f 0x6d
    | Fdiv -> instr8 f 0x6e
    | Ddiv -> instr8 f 0x6f
    | Irem -> instr8 f 0x70
    | Lrem -> instr8 f 0x71
    | Frem -> instr8 f 0x72
    | Drem -> instr8 f 0x73
    | Ineg -> instr8 f 0x74
    | Lneg -> instr8 f 0x75
    | Fneg -> instr8 f 0x76
    | Dneg -> instr8 f 0x77
    | Ishl -> instr8 f 0x78
    | Lshl -> instr8 f 0x79
    | Ishr -> instr8 f 0x7a
    | Lshr -> instr8 f 0x7b
    | Iushr-> instr8 f 0x7c
    | Lushr-> instr8 f 0x7d
    | Iand -> instr8 f 0x7e
    | Land -> instr8 f 0x7f
    | Ior  -> instr8 f 0x80
    | Lor  -> instr8 f 0x81
    | Ixor -> instr8 f 0x82
    | Lxor -> instr8 f 0x83
    | Iinc (ind, i) -> instr8 f 0x84; instr8 f ind; instr8 f i; 
    | I2l  -> instr8 f 0x85
    | I2f  -> instr8 f 0x86
    | I2d  -> instr8 f 0x87
    | L2i  -> instr8 f 0x88
    | L2f  -> instr8 f 0x89
    | L2d  -> instr8 f 0x8a
    | F2i  -> instr8 f 0x8b
    | F2l  -> instr8 f 0x8c
    | F2d  -> instr8 f 0x8d
    | D2i  -> instr8 f 0x8e
    | D2l  -> instr8 f 0x8f
    | D2f  -> instr8 f 0x90
    | I2b  -> instr8 f 0x91
    | I2c  -> instr8 f 0x92
    | I2s  -> instr8 f 0x93
    | Lcmp -> instr8 f 0x94
    | Fcmpl -> instr8 f 0x95
    | Fcmpg -> instr8 f 0x96
    | Dcmpl -> instr8 f 0x97
    | Dcmpg -> instr8 f 0x98
    | Ifeq i -> instr8 f 0x99; instr16 f i
    | Ifne i -> instr8 f 0x9a; instr16 f i
    | Iflt i -> instr8 f 0x9b; instr16 f i
    | Ifge i -> instr8 f 0x9c; instr16 f i
    | Ifgt i -> instr8 f 0x9d; instr16 f i
    | Ifle i -> instr8 f 0x9e; instr16 f i
    | If_icmpeq i -> instr8 f 0x9f; instr16 f i
    | If_icmpne i -> instr8 f 0xa0; instr16 f i
    | If_icmplt i -> instr8 f 0xa1; instr16 f i
    | If_icmpge i -> instr8 f 0xa2; instr16 f i
    | If_icmpgt i -> instr8 f 0xa3; instr16 f i
    | If_icmple i -> instr8 f 0xa4; instr16 f i
    | If_acmpeq i -> instr8 f 0xa5; instr16 f i
    | If_acmpne i -> instr8 f 0xa6; instr16 f i
    | Goto i -> instr8 f 0xa7; instr16 f i
    | Jsr -> instr8 f 0xa8
    | Ret -> instr8 f 0xa9
    | Tableswitch -> instr8 f 0xaa 
    | Lookupswitch -> instr8 f 0xab 
    | Ireturn -> instr8 f 0xac
    | Lreturn -> instr8 f 0xad
    | Freturn -> instr8 f 0xae
    | Dreturn -> instr8 f 0xaf
    | Areturn -> instr8 f 0xb0
    | Return -> instr8 f 0xb1
    | Getstatic i -> instr8 f 0xb2; instr16 f (i + 1) (* 0xb2 get static field *)
    | Putstatic i -> instr8 f 0xb3; instr16 f (i + 1) (* 0xb3 put static field *)
    | Getfield i -> instr8 f 0xb4; instr16 f (i + 1) (* 0xb4 get nonstatic field *)
    | Putfield i -> instr8 f 0xb5; instr16 f (i + 1) (* 0xb5 put nonstatic field *)
    | Invokevirtual i -> instr8 f 0xb6; instr16 f (i + 1) (* 0xb6 invoke virtual *)
    | Invokespecial i -> instr8 f 0xb7; instr16 f (i + 1) (* 0xb7 invoke special *)
    | Invokestatic i -> instr8 f 0xb8; instr16 f (i + 1) (* 0xb8 invoke static *)
    | Invokeinterface i -> instr8 f 0xb9; (* float_to_bytes: there should be more parameters passed to Invokeinterface, I think *) (* 0xb9 invoke interface *)
    | Unused -> instr8 f 0xba (* 0xba unused *)
    | New i -> instr8 f 0xbb; instr16 f (i + 1) (* 0xbb new *)
    | Newarray a -> (instr8 f 0xbc;  (* 0xbc new array *)
(* float_to_bytes: pull these out*)match a with
                        Abool -> instr8 f 4
                      | Abyte -> instr8 f 8
                      | Achar -> instr8 f 5
                      | Adouble -> instr8 f 7
                      | Afloat -> instr8 f 6
                      | Aint -> instr8 f 10 
                      | Along -> instr8 f 11
                      | Ashort -> instr8 f 9)
    | Anewarray i -> instr8 f 0xbd; instr16 f (i + 1) (* 0xbd new reference array *)
    | Arraylength -> instr8 f 0xbe
    | Athrow -> instr8 f 0xbf
    | Checkcast -> instr8 f 0xc0
    | Instanceof -> instr8 f 0xc1
    | Monitorenter -> instr8 f 0xc2
    | Monitorexit -> instr8 f 0xc3
    | Wide -> instr8 f 0xc4
    | Multianewarray (ind, i) -> instr8 f 0xc5; instr16 f (ind + 1); instr8 f i (* 0xc5 new multi reference array *)
    | Ifnull -> instr8 f 0xc6
    | Ifnonnull -> instr8 f 0xc7
    | Goto_w -> instr8 f 0xc8
    | Jsr_w -> instr8 f 0xc9
    | Breakpoint -> instr8 f 0xca
    | Impdep1 -> instr8 f 0xfe
    | Impdep2 -> instr8 f 0xff

let xor_flags (fs) : int =
  let xor_flag (flag:int) f : int = 
    match f with     
        A.Abstract -> (flag lor 0x0400)
      | A.Final -> (flag lor 0x0010)
      | A.Native -> (flag lor 0x0100)
      | A.Private -> (flag lor 0x002)
      | A.Protected -> (flag lor 0x0004)
      | A.Public -> (flag lor 0x0001)
      | A.Static -> (flag lor 0x0008)
      | A.Strictfp -> (flag lor 0x0800)
      | A.Synchronized -> (flag lor 0x0020)
      | A.Transient -> (flag lor 0x0080)
      | A.Volatile -> (flag lor 0x0040)
  in List.fold_left xor_flag 0 fs
     

(** Write the access flags for this class *)
let write_accessflags (f:out_channel) (c:cfile) : unit = 
   instr16 f (xor_flags c.flags)

exception Found of int
let index_of (arr:'a array) (f:'a -> bool) : int = 
  let index_aux _ = 
    Array.iteri (fun i x -> if f x then raise (Found i)) arr;
    raise Not_found
  in try index_aux () with Found i -> i | _ -> raise Not_found
  
(** Write the fields or methods -- depending on what we're called on *)
let write_fields_or_methods (f:out_channel) (c:cfile) (fs:finfo list): unit = 
  instr16 f (List.length fs); (* field table length *)
  let write_field ((flags, descindex, nindex, attrs):finfo) : unit = 
    instr16 f (xor_flags flags); 
    instr16 f (nindex + 1);
    instr16 f (descindex + 1); 
    instr16 f (List.length attrs); (* Attrs len *)
    let write_handler ((l1, l2, l3, is):handler) : unit = 
      instr16 f l1;(*(label_to_int l1);*)
      instr16 f l2;(*(label_to_int l2); *)
      instr16 f l3;(*(label_to_int l3); *)
      List.iter (fun x -> instr16 f (x + 1)) is (* float_to_bytes: is that right? +1? *)
    in let write_attr ((Acode (i, (i1, i2, ops, hs))):attr) : unit =
      instr16 f (i + 1); 
      let opcode_len = List.fold_left (+) 0 (List.map size ops) in 
        instr32 f (Int32.of_int (12 + (* initial bytes *)
                   opcode_len + (* code length *)
                   8*(List.length hs) (* exception table length *)
                    ));
        debug_string (Printf.sprintf "max_stack %d max_locals %d" i1 i2);
        instr16 f 1024;(*i1; max_stack <--float_to_bytes*)
        instr16 f 1024;(*i2; max_locals *)
        instr32 f (Int32.of_int opcode_len); (* code_len *)
        debug_string (Printf.sprintf "code_len: %d " opcode_len);
        List.iter (write_opcode f) ops;
        instr16 f (List.length hs); (* exception table len *)
        List.iter write_handler hs; (* write exception handler table *)
        instr16 f 0; (* attributes_count *)
    in List.iter write_attr attrs (* write attribute handler *)
  in List.iter write_field fs (* write field table *)

let write_fields (f:out_channel) (c:cfile) : unit = 
  write_fields_or_methods f c c.fields

let write_methods (f:out_channel) (c:cfile) : unit =
  write_fields_or_methods f c c.methods

(** This writes the entire cfile to the file *)
let write (c:cfile) : unit = 
  let fd = open_out_bin c.dst in 
    debug_string (Printf.sprintf "** writing class %s" c.dst);
    write_magic fd;
    write_versions fd;
    write_cpool fd c.pool;
    write_accessflags fd c;
    write_thisclass fd c;
    write_superclass fd c;
    write_interfaces fd c;
    write_fields fd c;
    write_methods fd c;
    instr16 fd 0000; (* <-- float_to_bytes? *)

