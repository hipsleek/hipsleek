(* unzip.ml - unpack zip/jar archives for OCaml *)
(* written by Xavier Leroy, INRIA Rocquencourt *)

(***********************************************************************)
(*                                                                     *)
(*                         The CamlZip library                         *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License.         *)
(*                                                                     *)
(***********************************************************************)

(* This module provides functions for reading and writing ZIP archive
   files.  ZIP archives package one or more compressed files into
   a single ``ZIP file'' along with information about the files,
   including file name, date and time of last modification, user-provided
   comments, and a checksum to verify the integrity of each entry.
   The entries of a ZIP file are not necessarily actual files, and can
   actually consist of arbitrary data.

   The ZIP file format used in this module is identical to that
   implemented by the popular [pkzip] archiver under Windows,
   and by the Info-ZIP [zip] and [unzip] commands under Unix and Windows.
   This format is also identical to the JAR file format used by Java. *)


exception ZError of string * string

let _ =
  Callback.register_exception "Error" (ZError("",""))

type stream

type flush_command =
    Z_NO_FLUSH
  | Z_SYNC_FLUSH
  | Z_FULL_FLUSH
  | Z_FINISH

(*Bachle: Changed here by removing this portion of code to adapt to newest Ocaml*)
(*
external deflate_init: int -> bool -> stream = "camlzip_deflateInit"
external deflate:
  stream -> string -> int -> int -> string -> int -> int -> flush_command
         -> bool * int * int
  = "camlzip_deflate_bytecode" "camlzip_deflate"
external deflate_end: stream -> unit = "camlzip_deflateEnd"*)

external inflate_init: bool -> stream = "camlzip_inflateInit"
external inflate:
  stream -> string -> int -> int -> string -> int -> int -> flush_command
         -> bool * int * int
  = "camlzip_inflate_bytecode" "camlzip_inflate"
external inflate_end: stream -> unit = "camlzip_inflateEnd"

external update_crc: int32 -> string -> int -> int -> int32
                   = "camlzip_update_crc32"

let buffer_size = 1024

let uncompress ?(header = true) refill flush =
  let inbuf = String.create buffer_size
  and outbuf = String.create buffer_size in
  let zs = inflate_init header in
  let rec uncompr inpos inavail =
    if inavail = 0 then begin
      let incount = refill inbuf in
      if incount = 0 then uncompr_finish true else uncompr 0 incount
    end else begin
      let (_, used_in, used_out) =
        inflate zs inbuf inpos inavail outbuf 0 buffer_size Z_SYNC_FLUSH in
      flush outbuf used_out;
      uncompr (inpos + used_in) (inavail - used_in)
    end
  and uncompr_finish first_finish =
    (* Gotcha: if there is no header, inflate requires an extra "dummy" byte
       after the compressed stream in order to complete decompression
       and return finished = true. *)
    let dummy_byte = if first_finish && not header then 1 else 0 in
    let (finished, _, used_out) =
       inflate zs inbuf 0 dummy_byte outbuf 0 buffer_size Z_SYNC_FLUSH in
    flush outbuf used_out;
    if not finished then uncompr_finish false
  in
    uncompr 0 0;
    inflate_end zs

exception Error of string * string * string

let read1 = input_byte
let read2 ic =
  let lb = read1 ic in let hb = read1 ic in lb lor (hb lsl 8)
let read4 ic =
  let lw = read2 ic in let hw = read2 ic in
  Int32.logor (Int32.of_int lw) (Int32.shift_left (Int32.of_int hw) 16)
let read4_int ic =
  let lw = read2 ic in let hw = read2 ic in
  if hw > max_int lsr 16 then raise (Error("", "", "32-bit data too large"));
  lw lor (hw lsl 16)
let readstring ic n =
  let s = String.create n in
  really_input ic s 0 n; s

let write1 = output_byte
let write2 oc n =
  write1 oc n; write1 oc (n lsr 8)
let write4 oc n =
  write2 oc (Int32.to_int n);
  write2 oc (Int32.to_int (Int32.shift_right_logical n 16))
let write4_int oc n =
  write2 oc n;
  write2 oc (n lsr 16)
let writestring oc s =
  output oc s 0 (String.length s)

type compression_method = Stored | Deflated

type entry =
  { filename: string;
    extra: string;
    comment: string;
    methd: compression_method;
    mtime: float;
    crc: int32;
    uncompressed_size: int;
    compressed_size: int;
    is_directory: bool;
    file_offset: int }

type in_file =
  { if_filename: string;
    if_channel: Pervasives.in_channel;
    if_entries: entry list;
    if_directory: (string, entry) Hashtbl.t;
    if_comment: string }

let entries ifile = ifile.if_entries
let comment ifile = ifile.if_comment

type out_file =
  { of_filename: string;
    of_channel: Pervasives.out_channel;
    mutable of_entries: entry list;
    of_comment: string }

exception Error of string * string * string

(* Return the position of the last occurrence of s1 in s2, or -1 if not
   found. *)

let strrstr pattern buf ofs len =
  let rec search i j =
    if i < ofs then -1
    else if j >= String.length pattern then i
    else if pattern.[j] = buf.[i + j] then search i (j+1)
    else search (i-1) 0
  in search (ofs + len - String.length pattern) 0

(* Determine if a file name is a directory (ends with /) *)

let filename_is_directory name =
  String.length name > 0 && name.[String.length name - 1] = '/'

(* Convert between Unix dates and DOS dates *)

let unixtime_of_dostime time date =
  fst(Unix.mktime
        { Unix.tm_sec = (time lsl 1) land 0x3e;
          Unix.tm_min = (time lsr 5) land 0x3f;
          Unix.tm_hour = (time lsr 11) land 0x1f;
          Unix.tm_mday = date land 0x1f;
          Unix.tm_mon = ((date lsr 5) land 0xf) - 1;
          Unix.tm_year = ((date lsr 9) land 0x7f) + 80;
          Unix.tm_wday = 0;
          Unix.tm_yday = 0;
          Unix.tm_isdst = false })

let dostime_of_unixtime t =
  let tm = Unix.localtime t in
  (tm.Unix.tm_sec lsr 1
     + (tm.Unix.tm_min lsl 5)
     + (tm.Unix.tm_hour lsl 11),
   tm.Unix.tm_mday
     + (tm.Unix.tm_mon + 1) lsl 5
     + (tm.Unix.tm_year - 80) lsl 9)

(* Read end of central directory record *)

let read_ecd filename ic =
  let buf = String.create 256 in
  let filelen = in_channel_length ic in
  let rec find_ecd pos len =
    (* On input, bytes 0 ... len - 1 of buf reflect what is at pos in ic *)
    if pos <= 0 || filelen - pos >= 0x10000 then
      raise (Error(filename, "",
                   "end of central directory not found, not a ZIP file"));
    let toread = min pos 128 in
    (* Make room for "toread" extra bytes, and read them *)
    String.blit buf 0 buf toread (256 - toread);
    let newpos = pos - toread in
    seek_in ic newpos;
    really_input ic buf 0 toread;
    let newlen = min (toread + len) 256 in
    (* Search for magic number *)
    let ofs = strrstr "PK\005\006" buf 0 newlen in
    if ofs < 0 || newlen < 22 || 
       (let comment_len = 
          Char.code buf.[ofs + 20] lor (Char.code buf.[ofs + 21] lsl 8) in
        newpos + ofs + 22 + comment_len <> filelen) then
      find_ecd newpos newlen
    else
      newpos + ofs in
  seek_in ic (find_ecd filelen 0);
  let magic = read4 ic in
  let disk_no = read2 ic in
  let cd_disk_no = read2 ic in
  let _ = read2 ic in                   (* disk_entries *)
  let cd_entries = read2 ic in
  let _ = read4_int ic in               (* cd_size *)
  let cd_offset = read4_int ic in
  let comment_len = read2 ic in
  let comment = readstring ic comment_len in
  assert (magic = Int32.of_int 0x06054b50);
  if disk_no <> 0 || cd_disk_no <> 0 then
    raise (Error(filename, "", "multi-disk ZIP files not supported"));
  (cd_entries, cd_offset, comment)

(* Read central directory *)

let read_cd filename ic cd_entries cd_offset =
  try
    seek_in ic cd_offset;
    let e = ref [] in
    for num_entry = 1 to cd_entries do
      let magic = read4 ic in
      let _ = read2 ic in               (* version_made_by *)
      let _ = read2 ic in               (* version_needed *)
      let flags = read2 ic in
      let methd = read2 ic in
      let lastmod_time = read2 ic in
      let lastmod_date = read2 ic in
      let crc = read4 ic in
      let compr_size = read4_int ic in
      let uncompr_size = read4_int ic in
      let name_len = read2 ic in
      let extra_len = read2 ic in
      let comment_len = read2 ic in
      let _ = read2 ic in               (* disk_number *)
      let _ = read2 ic in               (* internal_attr *)
      let _ = read4 ic in               (* external_attr *)
      let header_offset = read4_int ic in
      let name = readstring ic name_len in
      let extra = readstring ic extra_len in
      let comment = readstring ic comment_len in
      if magic <> Int32.of_int 0x02014b50 then
        raise (Error(filename, name,
                     "wrong file header in central directory"));
      if flags land 1 <> 0 then
        raise (Error(filename, name, "encrypted entries not supported"));

      e := { filename = name;
             extra = extra;
             comment = comment;
             methd = (match methd with
                         0 -> Stored
                       | 8 -> Deflated
                       | _ -> raise (Error(filename, name,
                                           "unknown compression method")));
             mtime = unixtime_of_dostime lastmod_time lastmod_date;
             crc = crc;
             uncompressed_size = uncompr_size;
             compressed_size = compr_size;
             is_directory = filename_is_directory name;
             file_offset = header_offset
           } :: !e
    done;
    List.rev !e
  with End_of_file ->
    raise (Error(filename, "", "end-of-file while reading central directory"))

(* Open a ZIP file for reading *)

let open_in filename =
  let ic = Pervasives.open_in_bin filename in
  let (cd_entries, cd_offset, cd_comment) = read_ecd filename ic in
  let entries = read_cd filename ic cd_entries cd_offset in
  let dir = Hashtbl.create (cd_entries / 3) in
  List.iter (fun e -> Hashtbl.add dir e.filename e) entries;
  { if_filename = filename;
    if_channel = ic;
    if_entries = entries;
    if_directory = dir;
    if_comment = cd_comment }

(* Close a ZIP file opened for reading *)

let close_in ifile =
  Pervasives.close_in ifile.if_channel

(* Return the info associated with an entry *)

let find_entry ifile name =
  Hashtbl.find ifile.if_directory name

(* Position on an entry *)

let goto_entry ifile e =
  try
    let ic = ifile.if_channel in
    seek_in ic e.file_offset;
    let magic = read4 ic in
    let _ = read2 ic in                 (* version_needed *)
    let _ = read2 ic in                 (* flags *)
    let _ = read2 ic in                 (* methd *)
    let _ = read2 ic in                 (* lastmod_time x*)
    let _ = read2 ic in                 (* lastmod_date *)
    let _ = read4 ic in                 (* crc *)
    let _ = read4_int ic in             (* compr_size *)
    let _ = read4_int ic in             (* uncompr_size *)
    let filename_len = read2 ic in
    let extra_len = read2 ic in
    if magic <> Int32.of_int 0x04034b50 then
       raise (Error(ifile.if_filename, e.filename, "wrong local file header"));
    (* Could validate information read against directory entry, but
       what the heck *)
    seek_in ifile.if_channel (e.file_offset + 30 + filename_len + extra_len)
  with End_of_file ->
    raise (Error(ifile.if_filename, e.filename, "truncated local file header"))

(* Read the contents of an entry as a string *)

let read_entry ifile e =
  try
    goto_entry ifile e;
    let res = String.create e.uncompressed_size in
    match e.methd with
      Stored ->
        if e.compressed_size <> e.uncompressed_size then
          raise (Error(ifile.if_filename, e.filename,
                       "wrong size for stored entry"));
        really_input ifile.if_channel res 0 e.uncompressed_size;
        res
    | Deflated ->
        let in_avail = ref e.compressed_size in
        let out_pos = ref 0 in
        begin try
          uncompress ~header:false
            (fun buf ->
              let read = input ifile.if_channel buf 0
                               (min !in_avail (String.length buf)) in
              in_avail := !in_avail - read;
              read)
            (fun buf len ->
              if !out_pos + len > String.length res then
                raise (Error(ifile.if_filename, e.filename,
                             "wrong size for deflated entry (too much data)"));
              String.blit buf 0 res !out_pos len;
              out_pos := !out_pos + len)
        with ZError(_, _) ->
          raise (Error(ifile.if_filename, e.filename, "decompression error"))
        end;
        if !out_pos <> String.length res then
          raise (Error(ifile.if_filename, e.filename,
                       "wrong size for deflated entry (not enough data)"));
        let crc = update_crc Int32.zero res 0 (String.length res) in
        if crc <> e.crc then
          raise (Error(ifile.if_filename, e.filename, "CRC mismatch"));
        res
  with End_of_file ->
    raise (Error(ifile.if_filename, e.filename, "truncated data"))
    
(* Write the contents of an entry into an out channel *)

let copy_entry_to_channel ifile e oc =
  try
    goto_entry ifile e;
    match e.methd with
      Stored ->
        if e.compressed_size <> e.uncompressed_size then
          raise (Error(ifile.if_filename, e.filename,
                       "wrong size for stored entry"));
        let buf = String.create 4096 in
        let rec copy n =
          if n > 0 then begin
            let r = input ifile.if_channel buf 0 (min n (String.length buf)) in
            output oc buf 0 r;
            copy (n - r)
          end in
        copy e.uncompressed_size
    | Deflated ->
        let in_avail = ref e.compressed_size in
        let crc = ref Int32.zero in
        begin try
          uncompress ~header:false
            (fun buf ->
              let read = input ifile.if_channel buf 0
                               (min !in_avail (String.length buf)) in
              in_avail := !in_avail - read;
              read)
            (fun buf len ->
              output oc buf 0 len;
              crc := update_crc !crc buf 0 len)
        with ZError(_, _) ->
          raise (Error(ifile.if_filename, e.filename, "decompression error"))
        end;
        if !crc <> e.crc then
          raise (Error(ifile.if_filename, e.filename, "CRC mismatch"))
  with End_of_file ->
    raise (Error(ifile.if_filename, e.filename, "truncated data"))
    
(* Write the contents of an entry to a file *)

let copy_entry_to_file ifile e outfilename =
  let oc = open_out_bin outfilename in
  try
    copy_entry_to_channel ifile e oc;
    close_out oc;
    begin try
      Unix.utimes outfilename e.mtime e.mtime
    with Unix.Unix_error(_, _, _) | Invalid_argument _ -> ()
    end
  with x ->
    close_out oc;
    Sys.remove outfilename;
    raise x

let filename (e:entry) : string = e.filename


(* stse 2006-0209: for the new interface *)
type zip = in_file
let name = filename
let load = open_in
let all = entries
let find = find_entry
let read = read_entry
