#include "xdebug.cppo"
(**/**)
open GUtil.SourceUtil
open GProcList
(**/**)

(**
   Entailment list view
*)
class entailment_list ?(model = new procedure_list_model ()) () =
  object (self)
    inherit procedure_list ~model () as super

    initializer
      name_col#set_title "Entailment"

    method get_selected_entailment () =
      super#get_selected_procedure ()

    method set_selected_entailment_validity valid =
      super#set_selected_procedure_validity valid

    method get_selected_entailment_validity () =
      super#get_selected_procedure_validity ()

    method update_source (src: string) : unit =
      model#update_source ~parse_func:parse_entailment_list src

  end

