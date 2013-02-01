(* regex.ml - regular expression matching for F# *)

module R = System.Text.RegularExpressions

type r = R.Regex
type m = R.Match

let rmatch (r:r) (x:string) : m = r.Match x
let is_match (r:r) (x:string) : bool = (r.Match x).Success
let success (m:m) : bool = m.Success

let rec get (i:int) (e:System.Collections.IEnumerator) : R.Group =
  if e.MoveNext () then if i=0 then (e.Current :?> R.Group) else get (i-1) e
  else failwith "no match"

let group (m:m) (i:int) : string = 
  (get i (m.Groups.GetEnumerator ())).Value

let split (r:r) (x:string) : string list = 
  Microsoft.FSharp.Compatibility.CompatArray.to_list (r.Split x)

(* replace r by x in x0 *)
let replace (r:r) (x:string) (x0:string) : string = r.Replace (x0, x)

let regex0 (x:string) : r = new R.Regex (x)

(* Very inefficient. Swap '\(' and '('. *)
let regex (x:string) : r = 
  let y1 = replace (regex0 "\\(") "\\\\(" x in
  let y2 = replace (regex0 "\\)") "\\\\)" y1 in
  let y3 = replace (regex0 "\\\\\\\\\(") "(" y2 in
  let y4 = replace (regex0 "\\\\\\\\\)") ")" y3 in
  new R.Regex (y4)
