hip_include 'msess/notes/node.ss'
hip_include 'msess/notes/hodef.ss'
hip_include 'msess/notes/commprimitives.ss'
hip_include 'msess/notes/fences.ss'

/************* GLOBAL VIEW: **************/

/* ************* no sync *************** */
/* pred_sess_prot G<B1,B2,S> ==  */
/*   B1->S: v#v::SString<_>;; */
/*   ((S->B1: v#v>0) * */
/*    ( S->B2: v#v>0) );; */
/*   B1->B2: v#v>=0;; */
/*   ((B2->S:1;;B2->S:v#v::Addr<_>;;S->B2:v#v::DDate<_,_,_>) or (B2->S:0)); */

/* ************* one sync *************** */
/* pred_sess_prot G<B1,B2,S,ssss> == */
/*   B1->S: v#v::SString<_>;;[B1,S]:Fp2<11,1,ssss> ;; */
/*   ((S->B1: v#v>0) * */
/*    ([B2,S]:Fm2<11,1,ssss,1.0> ;; S->B2: v#v>0) );; */
/*   B1->B2: v#v>=0;; */
/*   ((B2->S:1;;B2->S:v#v::Addr<_>;;S->B2:v#v::DDate<_,_,_>) or (B2->S:0)); */

/* ************* one3 fences *************** */
pred_sess_prot G<B1,B2,S,ssss> ==
  B1->S: v#v::SString<_>;;[B1,S]:Fp2<11,1,ssss> ;;
  (((S->B1: v#v>0);;[S,B1]:Fp2<22,1,ssss> ) *
   ([B2,S]:Fm2<11,1,ssss,1.0> ;; S->B2: v#v>0 ;;[S,B2]:Fp2<33,1,ssss> ) );;
   [B2,B1]:Fm2<22,1,ssss,1.0>;;
   [B1,B2]:Fm2<33,1,ssss,1.0>;;
   B1->B2: v#v>=0;;
  ((B2->S:1;;B2->S:v#v::Addr<_>;;S->B2:v#v::DDate<_,_,_>) or (B2->S:0));


SString getTitle()
  requires true
  ensures  res::SString<_>;

int getBudget()
  requires true
  ensures  res>=0;  

Addr getAddress()
  requires true
  ensures  res::Addr<_>;

int getQuote(SString s)
  requires s::SString<a>
  ensures  s::SString<a> & res>0;

DDate getDate(SString id, Addr addr)
  requires id::SString<i> * addr::Addr<a>
  ensures  id::SString<i> * addr::Addr<a> * res::DDate<_,_,_>;


void Buyer1(Channel s, Channel b2)
  /* requires s::Chan{@S !v#v::SString<_>;;?v#v>0}<> * b2::Chan{@S !v#v>=0}<>  */
  /* ensures  s::Chan{emp}<> * b2::Chan{emp}<> ;  */
  requires s::Chan{@S G<B1@prim,B2,S@sec,ccc>}<> * b2::Chan{@S  G<B1@prim,B2@sec,S,ccc>}<>
  ensures  s::Chan{emp}<> * b2::Chan{emp}<> ;
{
  SString book = getTitle();
  sends(s, book);
  int y1 = receive(s);
  send(b2, y1/2);
}

void Buyer2(Channel s, Channel b1)
  /* requires s::Chan{@S ?v#v>0;;((!1;;!v#v::Addr<_>;;?v#v::DDate<_,_,_>) or (!0))}<> * b1::Chan{@S ?v#v>=0}<>  */
  /* ensures  s::Chan{emp}<> * b1::Chan{emp}<> ; */
  requires s::Chan{@S G<B1,B2@prim,S@sec,ccc>}<> * b1::Chan{@S  G<B1@sec,B2@prim,S,ccc>}<>
  ensures  s::Chan{emp}<> * b1::Chan{emp}<> ;
{
  int budget = getBudget();
  Addr address = getAddress();
  int z1 = receive(s);
  int z2 = receive(b1);
  if (z1 - z2 <= budget){
    send (s,1);
    senda(s, address);
    DDate d = received(s);
  } else {
    send(s, 0);
  }
}

void Seller(Channel b1, Channel b2)
  /* requires b1::Chan{@S ?v#v::SString<_>;;!v#v>0}<> * b2::Chan{@S !v#v>0;;((?1;;?v#v::Addr<_>;;!v#v::DDate<_,_,_>) or (?0))}<> */
  /* ensures  b1::Chan{emp}<> * b2::Chan{emp}<> ; */
  requires b1::Chan{@S G<B1@sec,B2,S@prim,yyy>}<> * b2::Chan{@S  G<B1,B2@sec,S@prim,yyy>}<>
  ensures  b1::Chan{emp}<> * b2::Chan{emp}<> ;
{
  SString x1 = receives(b1);
  dprint;
  send(b1,getQuote(x1));
  dprint;
  send(b2,getQuote(x1));
  int answer = receive(b2);
  if (answer == 1) {
    Addr x2 = receivea(b2);
    sendd(b2, getDate(x1,x2)); 
  }
}



void Buyer1_fail(Channel s, Channel b2)
  /* requires s::Chan{@S !v#v::SString<_>;;?v#v>0}<> * b2::Chan{@S !v#v>=0}<>  */
  /* ensures  s::Chan{emp}<> * b2::Chan{emp}<> ;  */
  requires s::Chan{@S G<B1@prim,B2,S@sec,ccc>}<> * b2::Chan{@S  G<B1@prim,B2@sec,S,ccc>}<>
  ensures  s::Chan{emp}<> * b2::Chan{emp}<> ;
{
  SString book = getTitle();
   int y1 = receive(s);
   sends(s, book);
  send(b2, y1/2);
}
