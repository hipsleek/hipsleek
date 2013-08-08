let lem_pr = ref (fun (c:Cast.coercion_decl) -> "lem_store printer has not been initialized") 
let lem_eq = (==) 

class lemma_store =
object (self)
  val left_coercions = new Gen.stack_pr !lem_pr lem_eq
  val right_coercions = new Gen.stack_pr !lem_pr lem_eq
  val mutable any_left_lemma = false
  val mutable any_right_lemma = false
  method add_left_coercion lem =
    if lem!=[] then any_left_lemma <- true;
      left_coercions # push_list lem
  method add_right_coercion lem =
    if lem!=[] then any_right_lemma <- true;
      right_coercions # push_list lem
	  
  method set_left_coercion lem =
    left_coercions # reset ;
	self # add_left_coercion lem

  method set_right_coercion lem =
	right_coercions # reset ; 
	self # add_right_coercion lem 

  method clear_left_coercion =
    left_coercions # reset ;
	any_left_lemma <- false
	
  method clear_right_coercion =
	right_coercions # reset ; 
	any_right_lemma <- false
	
  method get_left_coercion =
    left_coercions # get_stk
  method get_right_coercion =
    right_coercions # get_stk
  method any_lemma =
    any_left_lemma || any_right_lemma
  method any_left_lemma =
    any_left_lemma 
  method any_right_lemma =
    any_right_lemma
end;;

let all_lemma = new lemma_store



