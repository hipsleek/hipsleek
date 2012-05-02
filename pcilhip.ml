open Cil
open Pretty
module E = Errormsg

let debug = false

class hipVisitor = object
  inherit nopCilVisitor

  method vvrbl (vinfo : varinfo) =
    
    DoChildren

  method vglob (g : global) =
    print_endline "global";
    DoChildren

end

let hip_transform (f : file) : unit =
  visitCilFile (new hipVisitor) f

let feature : featureDescr = 
  { fd_name = "hip";
    fd_enabled = ref false;
    fd_description = "transform to HIP format";
    fd_extraopt = [];
    fd_doit = hip_transform;
    fd_post_check = true;
  } 
