hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/cdl.ss'

/************* GLOBAL VIEW: **************/
/*********  where ;; is ;{_SS}  ***********/
/*****************************************/
/* pred_sess_prot G<A,B,C> == (A->B:1 * A->C:1);;B->C:2;   */
/* pred_sess_prot G<A,B,C> == (A->B:1 * A->C:1);;CDL(10);;B->C:2;   */
pred_sess_prot Gd<A,B,C,c> == ((A->B:1;;[B,A]:downd<c,10>) * (A->C:1;;[C,A]:downd<c,10>));;[C,B]:await<c,10>;;B->C:2;


void A(Channel a, Channel b, CDL c)
  /* requires a::Chan{@S ?1;;downv<c,1,10>}<> * b::Chan{@S await<c,10>;;!1}<>  */
  /* ensures  a::Chan{emp}<> * b::Chan{emp}<>; */
  requires a::Chan{@S Gd<A@prim,B@sec,C,c>}<> * b::Chan{@S Gd<A@prim,B,C@sec,c>}<> 
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<0,_>;
{
  send(a,1);
  DOWN(c);
  send(b,1);
  DOWN(c);
}


void A1(Channel a, Channel b, CDL c)
  /* requires a::Chan{@S ?1;;downv<c,1,10>}<> * b::Chan{@S await<c,10>;;!1}<>  */
  /* ensures  a::Chan{emp}<> * b::Chan{emp}<>; */
  requires a::Chan{@S Gd<A@prim,B@sec,C,c>}<> * b::Chan{@S Gd<A@prim,B,C@sec,c>}<> 
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<0,_>;
{
  send(a,1);
  send(b,1);
  DOWN(c);
  DOWN(c);
  dprint;
}


/* should fail */
void A2(Channel a, Channel b, CDL c)
  /* requires a::Chan{@S ?1;;downv<c,1,10>}<> * b::Chan{@S await<c,10>;;!1}<>  */
  /* ensures  a::Chan{emp}<> * b::Chan{emp}<>; */
  requires a::Chan{@S Gd<A@prim,B@sec,C,c>}<> * b::Chan{@S Gd<A@prim,B,C@sec,c>}<> 
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<0,_>;
{
  send(a,1);
  send(b,1);
  DOWN(c);
  dprint;
  // DOWN(c);
}
/* why id? 
      (exists flted_17_3218: a'::Chan{ . emp&{FLOW,(4,5)=__norm#E}}<>@M * 
                        b'::Chan{ . emp&{FLOW,(4,5)=__norm#E}}<>@M * 
                        c'::CNT<flted_17_3218,id>@M& 
                        flted_17_3218=1 & id=10 & a'=a & b'=b & c'=c&{FLOW,(4,5)=__norm#E})
*/


void B(Channel a, Channel b, CDL c)
  requires a::Chan{@S Gd<A@sec,B@prim,C,c>}<> * b::Chan{@S Gd<A,B@prim,C@sec,c>}<> * c::CNT<0,10>
  ensures  a::Chan{emp}<> * b::Chan{emp}<> * c::CNT<(-1),10>;
{
  int x = receive(a);
  dprint;
  AWAIT(c);
  dprint;
  send(b,2);
}
