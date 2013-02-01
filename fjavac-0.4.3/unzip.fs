(* unzip.fs - unpack zip/jar archives for F# *)

module Z = ICSharpCode.SharpZipLib.Zip

type zip = Z.ZipFile
type entry = Z.ZipEntry

let rec enum_to_list (e:System.Collections.IEnumerator) : entry list =
  if not (e.MoveNext ()) then []
  else (e.Current :?> entry) :: enum_to_list e

let read (z:zip) (e:entry) : string =
  let s = z.GetInputStream e in
  let n = Int64.to_int e.Size in
  let a = Bytearray.make n in
  assert (s.Read (a, 0, n) = n);
  Bytearray.ascii_to_string a

let load (x:string) : zip = new Z.ZipFile (x)
let name (e:entry) : string = e.Name
let all (z:zip) : entry list = enum_to_list (z.GetEnumerator ())

let find (z:zip) (x:string) : entry = 
  let e = z.GetEntry x in
  if e = null then raise Not_found else e
