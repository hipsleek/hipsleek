
open GEntailmentList
open Resource
open GSourceViewX
open GUtil
open GUtilSleek

module SU = SourceUtil
module FU = FileUtil
module SH = SleekHelper
module TP = Tpdispatcher

(*common: both hip and sleek*)
let set_theorem_prover id =
      let provers = [TP.OmegaCalc; TP.Mona; TP.Redlog] in
      let tp = List.nth provers id in
      TP.change_prover tp;
      let tp_name = TP.name_of_tp tp in
      log (Printf.sprintf "Use %s as backend prover." tp_name)

(*hip*)

(*sleek*)
