(**
   Sleek source view
 *)

open GUtil.SourceUtil

class sleek_source_view ?(text = "") () =

  let get_sleek_lang () =
    let lang_mime_type = "text/x-sleek" in
    let language_manager = GSourceView2.source_language_manager ~default:true in
    match language_manager#guess_language ~content_type:lang_mime_type () with
    | None -> failwith ("no language for " ^ lang_mime_type)
    | Some lang -> lang
  in

  object (self)
    inherit GSourceViewX.source_view ~text () as super
    
    initializer
      super#source_buffer#set_language (Some (get_sleek_lang ()));
      super#source_buffer#set_highlight_syntax true;

    (** highlight checkentail command
       by applying checkentail tag on that part of source code *)
    method hl_entailment (e: entailment): unit =
      super#hl_segment ~clear_previous_highlight:true ~scroll:true e.pos

    (** highlight all checkentail commands *)
    method hl_all_entailement () : unit =
      let src = self#source_buffer#get_text () in
      let e_list = parse_entailment_list src in
      List.iter (fun e -> super#hl_segment e.pos) e_list

  end

