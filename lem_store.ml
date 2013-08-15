open Gen.Basic
open Gen.BList

let lem_pr = ref (fun (c:Cast.coercion_decl) -> "lem_store printer has not been initialized") 
let ilem_pr = ref (fun (c:Iast.coercion_decl) -> "COERC printer has not been initialized") 
let ilem_lst_pr = ref (fun (c:Iast.coercion_decl_list) -> "COERC_LIST printer has not been initialized") 
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

  method add_coercion_x left right =
    self # add_left_coercion left;
    self # add_right_coercion right

  method add_coercion left right =
    let pr x = string_of_int (List.length x) in
    Debug.no_1 "lem_store:add_coercion" (add_str "(left,right)" (pr_pair pr pr)) 
        pr_none 
        (fun _ -> self # add_coercion_x left right) (left,right)

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

  method pop_coercion_x =
    self # pop_left_coercion;
    self # pop_right_coercion


  method pop_coercion =
    let left_num = num_left_lem_stk # top_no_exc in
    let right_num = num_right_lem_stk # top_no_exc in
    Debug.no_1 "lem_store:pop_coercion" 
        (add_str "(left,right)" (pr_pair string_of_int string_of_int)) 
        pr_none 
        (fun _ -> self # pop_coercion_x) (left_num,right_num)


end;;

let all_lemma = new lemma_store;;

(* module COERC = *)
(* struct *)
(*   type t = Iast.coercion_decl *)
(*   let eq = Iast.eq_coercion *)
(*   let string_of = !ilem_pr *)
(* end;; *)

(* module BL_coercs = Gen.BListEQ(COERC);; *)

(* module COERC_LIST = *)
(* struct *)
(*   type t = Iast.coercion_decl_list *)
(*   let eq = Iast.eq_coercion_list *)
(*   let string_of = !ilem_lst_pr *)
(* end;; *)


(* module BL_coercs_list = Gen.BListEQ(COERC_LIST);; *)

class lemma_list_store = 
object (self)
  val lst = new Gen.stack_pr !ilem_lst_pr Iast.eq_coercion_list

  method add_ilemma lemma_list =
    lst # push lemma_list

  method set_ilemma il_lst  =
    let _ = lst # reset in
    let len = List.iter (self # add_ilemma ) il_lst in
    ()

  method get_all_ilemma =
    lst # reverse_of

  method string_of =
    lst # string_of

end;;

let ilemma_st = new lemma_list_store;;


