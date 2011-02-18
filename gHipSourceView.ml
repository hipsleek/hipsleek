(**
   Hip source view
 *)

open GUtil.SourceUtil

class hip_source_view ?(text = "") () =

  let get_hip_lang () =
    (* TODO: syntax definition for hip *)
    let lang_mime_type = "text/x-sleek" in
    let language_manager = GSourceView2.source_language_manager ~default:true in
    match language_manager#guess_language ~content_type:lang_mime_type () with
    | None -> failwith ("no language for " ^ lang_mime_type)
    | Some lang -> lang
  in

  object (self)
    inherit GSourceViewX.source_view ~text () as super
    
    initializer
      super#source_buffer#set_language (Some (get_hip_lang ()));
      super#source_buffer#set_highlight_syntax true;

    method hl_proc (p: procedure): unit =
      super#hl_segment ~clear_previous_highlight:true ~scroll:true p.pos

  end

