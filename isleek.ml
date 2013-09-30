
open Globals

module I = Iast
module C = Cast
module CF = Cformula
module CP = Cpure
module IF = Iformula
module IP = Ipure


type tactics =
  | Match of id
  | ListAllCheckEntail of (id * meta_formula * meta_formula * (list_context option) * (proof option))
