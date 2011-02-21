
  type stree =
    | Leaf of bool (*false-> empty*)
    | Node of stree * stree
    
  let top = Leaf true
  let bot = Leaf false
  let leftTree = Node ((Leaf true), (Leaf false))  
  let rightTree = Node ((Leaf false), (Leaf true))
  
  let rec empty = function
    | Leaf b -> not b 
    | Node (s0, s1) -> (empty s0)&&(empty s1)
  
  let rec full = function
    | Leaf b -> b
    | Node (s0, s1) -> (full s0)&&(full s1)
    
  let rec stree_eq t1 t2 = match t1,t2 with
    | Leaf b1,Leaf b2  -> b1==b2
    | Node (l1, r1), Node (l2,r2) -> (stree_eq l1 l2)&&(stree_eq r1 r2)
    | _ -> false
        
  let rec can_join x y = match x,y with
    | _ , Leaf false
    | Leaf false, _ -> true
    | Node(l1,r1),Node(l2,r2) -> (can_join l1 l2) && (can_join r1 r2)
    | _ -> false
    
  let rec norm t = match t with
    | Leaf b -> Leaf b
    | Node (l, r) -> match norm l,norm r with
        | Leaf b1, Leaf b2 when b1==b2 -> Leaf b1
        | nl,nr -> Node(nl,nr)
    
  let join x y =
    let rec helper x y= match x with
      | Leaf b -> if b then Leaf true else y
      | Node (l1, r1) -> match y with
        | Leaf b -> if b then Leaf true else x
        | Node (l2, r2) -> Node ((helper l1 l2), (helper r1 r2)) in
    if (can_join x y) then norm(helper x y) else bot
  
  let intersect x y =
    let rec helper x y= match x with
      | Leaf b -> if b then y else x
      | Node (l1, r1) -> match y with
        | Leaf b -> if b then x else y
        | Node (l2, r2) -> Node ((helper l1 l2), (helper r1 r2)) in
    norm(helper x y)
   
  let rec neg_tree = function
    | Leaf b -> Leaf (not b)
    | Node (l, r) -> Node ((neg_tree l), (neg_tree r))
        
  let rec multiply t1 t2= match t1 with
      | Leaf b -> if b then t2 else t1
      | Node (l, r) -> Node ((multiply l t2), (multiply r t2))
      
  let split x =(multiply x leftTree),(multiply x rightTree)

  let rec string_of_tree_share ts = match ts with
    | Leaf true -> "T"
    | Leaf false -> ""
    | Node (t1,t2) -> "("^(string_of_tree_share t1)^","^(string_of_tree_share t2)^")"
         