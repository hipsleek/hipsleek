(i) no sync needed:
  A->B ;; B->A
(ii) ghost fence (fence when (receiver_lhs = sender_rhs) and (sender_lhs != receiver_rhs)):
  A-> B ;; B->C
  A-> B ;; F(id) ;; B->C
  A-> B ;; (A,B):F+(id);; (C,B):F(id) ;; B->C
(iii) ghost fence (fence when (receiver_lhs = receiver_rhs) and (sender_lhs != sender_rhs)):
  A-> B ;; C->B
  A-> B ;; F(id) ;; C->B
  A-> B ;;  (A,B):F+(id);; (C,B):F(id) ;; C->B
(iv) dynamic sync (non-blocking send)
 B->A ;; B->C
(v) dynamic sync (no common party)
  A->B ;; C->D
               

A->B;;A->B;;Tail
A->B * A->C ;; B->D ;;Tail
A->B * A->C ;; F(id) ;; B->D ;;Tail
  
let last_transmissions s =
  match s with
  | R1->R2:..;;end   -> [(R1,R2)]
  | s1 or s2  -> (last_transmissions s1) \union (last_transmissions s2)
  | s1 * s2   -> (last_transmissions s1) \union (last_transmissions s2)
  | s1;;t     -> last_transmissions t

let first_transmissions s =
  match s with
  | R1->R2:..  -> [(R1,R2)]
  | s1 or s2  -> (first_transmissions s1) \union (first_transmissions s2)
  | s1 * s2   -> (first_transmissions s1) \union (first_transmissions s2)
  | s1;;t     -> first_transmissions s1

len []   = 0
len h::t = 1 + (len t)                 

first []   = Exception
first h::t = h
                 
count_agent x [] = 0
count_agent x h::t = if x==h then 1 + (count x t)
               else (count x t)

get_communication_agent map (A,B) = try map.find((A,B)) with Not_found -> map.find((B,A))

same_channel map P =
  comm = get_communication_agent map (first map P)
  return (len P == count_agent map comm P)


algo:
1. each pair of roles indetifies a channel --> map from pairs of roles to channels
2. refinement1: identify the sync locations
3. refinement2: instantiate sync instruments
4. apply the projection rules                                                                            


//identifying sync points
let refinement1 G map =
  match G with
  | s1;;end   -> s1;;end
  | s1 or s2  -> (refinement1 s1 map) or (refinement1 s2 map)
  | s1 * s2   -> (refinement1 s1 map) * (refinement1 s2 map)
  | s1;;s2;;t ->
     let s1 = refinement1 s1 map in
     let s2 = refinement1 s2 map in
     let t1 = last_transmissions s1 in
     let t2 = first_transmissions s2 in
     let peers_t1 = participants t1 in
     let peers_t2 = participants t2 in
     if same_channel map (peers_t1 \union peers_t2) then s1;;((refinement1 s2 map);;t)
     else s1 ;; F(fresh_id) ;; ((refinement1 s2 map);;t)


//instantiate sync instruments
let refinement2 G =
  match G with
  | s1;;end   -> s1;;end
  | s1 or s2  -> (refinement2 s1) or (refinement2 s2)
  | s1 * s2   -> (refinement2 s1) * (refinement2 s2)
  | s1;;F(id);;s2;;t ->
     let s1 = refinement2 s1 map in
     let s2 = refinement2 s2 map in
     let insert_acc_fence left_s share =
       match left_s with
       | sl1 sor sl2 -> (insert_acc_fence sl1 share) sor (insert_acc_fence sl2 share)
       | sl1 * sl2 -> (insert_acc_fence sl1 share/2) sor (insert_acc_fence sl2 share/2)
       | A->B ..;;end -> A->B:.. ;; F+(id,share) ;;end 
       | h;;t    -> insert_acc_fence t share
     in
     let insert_cons_fence right_s share =
       match right_s with
       | sl1 sor sl2 -> (insert_cons_fence sl1 share) sor (insert_cons_fence sl2 share)
       | sl1 * sl2 -> (insert_cons_fence sl1 share/2) sor (insert_cons_fence sl2 share/2)
       | A->B:..;;t    -> F(id,share) ;; right_s
     in
     let insert_count_down left_s share =
       match left_s with
       | sl1 sor sl2 -> (insert_acc_fence sl1 share) sor (insert_acc_fence sl2 share)
       | sl1 * sl2 -> (insert_acc_fence sl1 share/2) sor (insert_acc_fence sl2 share/2)
       | A->B ..;;end -> A->B:.. ;; B: F+(id,share) ;;end 
       | h;;t    -> insert_acc_fence t share
     in
     let insert_await right_s share =
       match right_s with
       | sl1 sor sl2 -> (insert_cons_fence sl1 share) sor (insert_cons_fence sl2 share)
       | sl1 * sl2 -> (insert_cons_fence sl1 share/2) sor (insert_cons_fence sl2 share/2)
       | A->B:..;;t    -> F(id,share) ;; right_s
     in

     let helper right_s share =
       match s1 with
       | sr1 sor sr2 -> (helper2 sr1 share) sor (helper2 sr2 share)
       | sl1 * sl2 -> (helper2 s1 share/2) sor (helper2 s2 share/2)
       | A->B ..;;end -> A->B:.. ;; F(id,share) ;;end (* fence or dynamic? *)
       | h;;t    -> helper2 t share
    in
     let t1 = last_transmissions s1 in
     let t2 = first_transmissions s2 in
     let peers_t1 = participants t1 in
     let peers_t2 = participants t2 in
     foreach 
     if (i) or (ii) then 
     if same_channel map (peers_t1 \union peers_t2) then s1;;((refinement1 s2 map);;t)
     else s1 ;; F(fresh_id) ;; ((refinement1 s2 map);;t)



 G<A,B,C,D> == A->B:1 ;; C->D:2
 G<A,B,C,D,c> ==A->B:1 ;; CDL(c) ;; C->D:2
 G<A,B,C,D,c> == A->B:1 ;; B:countDown(c) ;; C: await(c) ;; C->D:2.

  void foo(Channel ab, Channel cd)
       requires ab::Chan{ !1}<> * ab::Chan{ ?1}<> * cd::Chan{ !2}<> * cd::Chan{ ?2}<>
       ensures ab::Chan{ emp}<> * ab::Chan{ emp}<> * cd::Chan{ emp}<> * cd::Chan{ emp}<>
{
 CDL cdl = create_latch(1);
 par{}
   { case {}     ab::Chan{ !1}<> -> (* A *)
        send(ab,1);
     ||
     case {}     ab::Chan{ ?1}<> -> (* B *)
        int x = receive(ab);
        countDown(cdl);
     ||
     case {}     cd::Chan{ !2}<> -> (* C *)
        await(cdl);
        send(cd,2);
     ||
     case {}     cd::Chan{ ?2}<> -> (* D *)
        int y = receive(cd);
   }                       
}


//CountDownLatch
data CDL {}

data cell { int val; }

pred_prim LatchIn{-%P@Split}<>;

pred_prim LatchOut{+%P@Split}<>;

pred_prim CNT<n:int>
  inv n>=(-1);

lemma "split" self::CNT<n> & a>=0 & b>=0 & n=a+b -> self::CNT<a> * self::CNT<b>;

lemma "combine" self::CNT<a> * self::CNT<b> & a,b>=0 -> self::CNT<a+b>;

/********************************************/
CDL create_latch(int n) with %P
  requires n>0
  ensures res::LatchIn{-%P}<> * res::LatchOut{+%P}<> * res::CNT<n>;
  requires n=0
  ensures res::CNT<(-1)>;

void countDown(CDL c)
  requires c::LatchIn{-%P}<> * %P * c::CNT<n> & n>0
  ensures c::CNT<n-1>;
  requires c::CNT<(-1)> 
  ensures c::CNT<(-1)>;

void await(CDL c)
  requires c::LatchOut{+%P}<> * c::CNT<0>
  ensures c::CNT<(-1)> * %P;
  requires c::CNT<(-1)>
  ensures c::CNT<(-1)>;
