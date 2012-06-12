(*open Globals*)

module Ts = 
struct
  type stree =
    | Leaf of bool (*false-> empty*)
    | Node of stree * stree
  type t_sh = stree
  let top = Leaf true
  let bot = Leaf false
    
  let mkNode l r = match l,r with
    | Leaf b1, Leaf b2 when b1==b2 -> Leaf b1
    | _ -> Node(l,r)
    
  let rec empty = function
    | Leaf b -> not b 
    | Node (s0, s1) -> (empty s0)&&(empty s1)
  
  let rec full = function
    | Leaf b -> b
    | Node (s0, s1) -> (full s0)&&(full s1)
    
  let depth_0 = function 
	| Leaf _ -> true
	| Node _ -> false
  
  let rec depth = function 
	| Leaf _ -> 0
	| Node (l,r)-> 
		let l = depth l in
		let r = depth r in
		(if l>r then l else r)+1
	
  let rleft n = 
    let rec helper n c = match n with 
		| Leaf _ -> n
		| Node (l, r) -> if c=1 then l else mkNode (helper l (c-1)) (helper r (c-1)) in
	helper n (depth n)
   
  let rright n = 
    let rec helper n c = match n with 
		| Leaf _ -> n
		| Node (l, r) -> if c=1 then r else mkNode (helper l (c-1)) (helper r (c-1)) in
	helper n (depth n)
		  
  let rec eq t1 t2 = match t1,t2 with
    | Leaf b1,Leaf b2  -> b1==b2
    | Node (l1, r1), Node (l2,r2) -> (eq l1 l2)&&(eq r1 r2)
    | _ -> false
	 
  let stree_eq = eq
	  
  let rec string_of_tree_share ts = match ts with
    | Leaf true -> "T"
    | Leaf false -> ""
    | Node (t1,t2) -> "("^(string_of_tree_share t1)^","^(string_of_tree_share t2)^")"
	
  let string_of = string_of_tree_share
  
  
  (**********utilities , possibly needed **********)
  let rec stree_cmp t1 t2 = match t1,t2 with
	| Leaf false, Leaf false 
	| Leaf true, Leaf true -> 0
	| Leaf false, _ -> -1
	| Leaf true, _ -> 1
	| _, Leaf true -> -1
	| _, Leaf false -> 1
    | Node (l1, r1), Node (l2,r2) -> 
		let r = stree_cmp l1 l2 in
		if r=0 then stree_cmp r1 r2
		else r
		
  let rec can_join x y = match x,y with
    | _ , Leaf false
    | Leaf false, _ -> true
    | Node(l1,r1),Node(l2,r2) -> (can_join l1 l2) && (can_join r1 r2)
    | _ -> false
            
  (*returns the largest share, the smallest tree *)
  let join x y =
    let rec helper x y= match x with
      | Leaf b -> if b then Leaf true else y
      | Node (l1, r1) -> match y with
        | Leaf b -> if b then Leaf true else x
        | Node (l2, r2) -> mkNode (helper l1 l2) (helper r1 r2) in
    if (can_join x y) then helper x y else bot
  
(*returns the smallest share contained in both, the largest tree*)
  let rec intersect x y = match x with
      | Leaf b -> if b then y else x
      | Node (l1, r1) -> match y with
        | Leaf b -> if b then x else y
        | Node (l2, r2) -> mkNode (intersect l1 l2) (intersect r1 r2) 
   
  let rec neg_tree = function
    | Leaf b -> Leaf (not b)
    | Node (l, r) -> mkNode (neg_tree l) (neg_tree r)

  let rec string_of_tree_share ts = match ts with
    | Leaf true -> "T"
    | Leaf false -> ""
    | Node (t1,t2) -> "("^(string_of_tree_share t1)^","^(string_of_tree_share t2)^")"
	
  let rec contains x y = match x,y with
    | Leaf true, _ ->  true
    | _, Leaf false -> true
    | Leaf false, _ -> false
    | Node(l1,r1), Node(l2,r2) -> (contains l1 l2)&&(contains r1 r2)
    | Node _, Leaf true -> false
    
  let subtract x y = 
    let rec helper x y = match x,y with
      | Leaf true, _ -> neg_tree y
      | Leaf false, Leaf false -> y
      | Leaf false, _ -> failwith "missmatch in contains"
      | Node(l1,r1), Node(l2,r2) -> mkNode (helper l1 l2) (helper r1 r2) 
      | Node _ , Leaf false -> x
      | Node _ , Leaf true -> failwith "missmatch in contains" in      
   if contains x y then helper x y else bot
  let rec union x y = match x with
	| Leaf true -> x
	| Leaf false -> y
	| Node (x1,x2) -> match y with
		| Leaf true -> y
		| Leaf false -> x
		| Node (y1,y2) -> mkNode (union x1 y1) (union x2 y2)
    
    (*let leftTree = Node ((Leaf true), (Leaf false))  
  let rightTree = Node ((Leaf false), (Leaf true))*)
  
  let rec latex_of_share s = match s with 
    | Leaf b -> if b then "\\bullet" else "\\circ"
    | Node (s1,s2) -> " \\Tree [ $"^(latex_of_share s1)^"$ $"^(latex_of_share s2)^"$ ] "
  end     
  