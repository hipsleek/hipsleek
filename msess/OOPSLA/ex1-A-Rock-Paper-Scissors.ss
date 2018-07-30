/***********************/
/* Rock-Paper-Scissors */
/*  (simple messages)  */
/***********************/

hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'


pred_sess_prot G<C:role,S:role,c:chan> ==
     C->S:c(1000) ;;
     C->S:c(v#emp & 1<=v & v<=3);


// Player
void C(Channel c)
 requires c::Chan{@S G<C@peer,S,c@chan>}<>
 ensures  c::Chan{emp}<> ;
{
 send(c,1000)[int];
 send(c,3)[int];
}


// Server
void S(Channel c, int reward, int no_players)
 requires c::Chan{@S G<C,S@peer,c@chan>}<> * @full[reward] & reward>=0  // projection of G on (S,c)
 //requires c::Chan{@S ?1000 ;; ?v#(emp & 1<=v & v<=3) }<> & reward>=0
 ensures  c::Chan{emp}<> ;
{
 int fee    = receive(c)[int];
 int option = receive(c)[int];
 if (fee>=1000) { reward = reward + fee; }
 else { reward = 0; }
 dprint;
 assert reward'>=1000;
 assert reward'=0 | reward'>=1000;
 // dprint;
}
