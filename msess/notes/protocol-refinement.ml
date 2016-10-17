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
len h::t = 1 + len(t)                 

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
  | s1 or s2  -> (refinement2 s1 ) or (refinement2 s2)
  | s1 * s2   -> (refinement2 s1 ) * (refinement2 s2)
  | s1;;F(id);;s2;;t ->
     let s1 = refinement1 s1 map in
     let s2 = refinement1 s2 map in
     let t1 = last_transmissions s1 in
     let t2 = first_transmissions s2 in
     let peers_t1 = participants t1 in
     let peers_t2 = participants t2 in
     if same_channel map (peers_t1 \union peers_t2) then s1;;((refinement1 s2 map);;t)
     else s1 ;; F(fresh_id) ;; ((refinement1 s2 map);;t)    
