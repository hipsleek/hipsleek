
open Globals

module I = Iast
module C = Cast
module CF = Cformula
module CP = Cpure
module IF = Iformula
module IP = Ipure

type id = int

type tactics =
  | Match of id
  (*| CheckEntailInfor of (id * meta_formula * meta_formula * (CF.list_context option) * (Prooftracer.proof option))*)
  | ListCheckEntail 
  | Auto 

let string_of_tactics t =  match t with 
  |Match _-> "Match"
  |ListCheckEntail -> "ListCheckEntail"
  |Auto ->"Auto"
  (*|_ -> "TODO: string_of_command for this tactic"*)


