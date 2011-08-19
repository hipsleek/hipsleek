
open GEntailmentList
open Resource
open GSourceViewX
open GUtil
open GUtil_sleek

module SU = SourceUtil
module FU = FileUtil
module SH = SleekHelper
module TP = Tpdispatcher


let set_theorem_prover id =
      let provers = [TP.OmegaCalc; TP.Mona; TP.Redlog] in
      let tp = List.nth provers id in
      TP.change_prover tp;
      let tp_name = TP.name_of_tp tp in
      log (Printf.sprintf "Use %s as backend prover." tp_name)
