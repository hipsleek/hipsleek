let lem_pr = ref (fun (c:Cast.coercion_decl) -> "lem_store printer has not been initialized") 
let lem_eq = (==) 

class lemma_store =
object (self)
  val left_lem = new Gen.stack_pr !lem_pr lem_eq
  val right_lem = new Gen.stack_pr !lem_pr lem_eq
  val num_left_lem_stk = new Gen.stack_noexc 0 string_of_int (==)
  val num_right_lem_stk = new Gen.stack_noexc 0 string_of_int (==)
  val mutable num_left_lem = 0
  val mutable num_right_lem = 0

  method add_left_coercion lem =
    let len = List.length lem in
    if len>0 then num_left_lem <- num_left_lem + len;
      left_lem # push_list lem;
      num_left_lem_stk # push len

  method add_right_coercion lem =
    let len = List.length lem in
    if len>0 then num_right_lem <- num_right_lem + len;
      right_lem # push_list lem;
      num_right_lem_stk # push len

  method add_coercion left right =
    self # add_left_coercion left;
    self # add_right_coercion right

  method clear_left_coercion =
    left_lem # reset ;
    num_left_lem_stk # reset ;
    num_left_lem <- 0
	
  method clear_right_coercion =
    right_lem # reset ;
    num_right_lem_stk # reset ;
    num_right_lem <- 0

  method clear_coercion =
    self # clear_left_coercion;
    self # clear_right_coercion

  method set_left_coercion lem =
    self # clear_left_coercion;
    self # add_left_coercion lem

  method set_right_coercion lem =
    self # clear_right_coercion;
    self # add_right_coercion lem

  method set_coercion left right =
    self # set_left_coercion left;
    self # set_right_coercion right

  method get_left_coercion =
    left_lem # get_stk

  method get_right_coercion =
    right_lem # get_stk

  method any_coercion =
    num_left_lem>0 || num_right_lem>0
  method any_left_coercion =
    num_left_lem>0
  method any_right_coercion =
    num_left_lem>0


  method pop_left_coercion =
    let len = num_left_lem_stk # pop_top_no_exc in
    if len>0 then 
      begin
        num_left_lem <- num_left_lem - len;
        for i = 1 to len do
          left_lem # pop
        done
      end

  method pop_right_coercion =
    let len = num_right_lem_stk #  pop_top_no_exc in
    if len>0 then 
      begin
        num_right_lem <- num_right_lem - len;
        for i = 1 to len do
          right_lem # pop
        done
      end

  method pop_coercion =
    self # pop_left_coercion;
    self # pop_right_coercion

end;;

let all_lemma = new lemma_store



