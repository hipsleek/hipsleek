/*
in prelude.ss
data char_star {
  int val;
  char_star next;
}
*/

WSS<p> ==
  self::WFSeg<q>*q::char_star<0,p> 
  inv self!=null;

WFSeg<p> ==
  self=p 
  or self::char_star<v,q>*q::WFSeg<p> & v!=0
  inv true;

HeapPred P(char_star x).
//PostPred QQ(char_star x,char_star y,char_star z).
HeapPred QQ(char_star x,char_star y,char_star z).

void while1(ref char_star s)
  infer [QQ,@classic,@pure_field]
  requires s::WSS<p>
  ensures QQ(s,s',p);
/*
  requires s::WSS<p> 
  ensures s::WFSeg<s'>*s'::char_star<0,p> ;
*/
{
  int x=get_char(s);
  if (x!=0) {
    s = plus_plus_char(s);
    while1(s);
  }
}

/*
# ex13c.ss

[ // POST
(2;0)s::char_star<flted_10_1615,p>@M * GP_1662(s',s@NI)&
s'=s & flted_10_1615=0 |#|3  --> QQ(s,s',p)&
true,
 // POST
(2;0)emp&s'=s |#|3  --> GP_1662(s',s@NI)&
true,
 // POST
(1;0)s::char_star<v_1631,q>@M * GP_1661(q,s',p,s@NI)&
v_1631!=0 |#|3  --> QQ(s,s',p)&
true,
 // POST
(1;0)QQ(q,s',p)&true |#|3  --> GP_1661(q,s',p,s@NI)&
true]
--------------
For GP_1662
===========
(2;0)emp&s'=s |#|3  --> GP_1662(s',s@NI)&
//convert to predicate
GP_1662(s',s@NI) = s'=s

For GP_1662
===========
(1;0)QQ(q,s',p)&true |#|3  --> GP_1661(q,s',p,s@NI)&
//convert to predicate
GP_1661(q,s;,p,s) == QQ(q,s',p)


For QQ
=======
s::char_star<flted_10_1615,p>@M * GP_1662(s',s@NI)&
  s'=s & flted_10_1615=0 |#|3  --> QQ(s,s',p)&
// fold GP_1662
s::char_star<flted_10_1615,p>@M & s'=s &
  s'=s & flted_10_1615=0 |#|3  --> QQ(s,s',p)&


(1;0)s::char_star<v_1631,q>@M * GP_1661(q,s',p,s@NI)& v_1631!=0 |#|3  
  --> QQ(s,s',p)
// fold GP_1661
(1;0)s::char_star<v_1631,q>@M * QQ(q,s',p) & v_1631!=0 |#|3  
  --> QQ(s,s',p)

Combine Implications
--------------------
s::char_star<flted_10_1615,p>@M & s'=s &
  s'=s & flted_10_1615=0 |#|3  --> QQ(s,s',p)&
/\ s::char_star<v_1631,q>@M * QQ(q,s',p) & v_1631!=0 |#|3  
  --> QQ(s,s',p)

s::char_star<flted_10_1615,p>@M & s'=s & s'=s & flted_10_1615=0 |#|3  
\/ (s::char_star<v_1631,q>@M * QQ(q,s',p) & v_1631!=0 |#|3  
  --> QQ(s,s',p)

  A \/ C -> B
------------------
 A -> B /\ C -> B

  A -> B /\ C
-------------------
 A -> B /\ A -> C

  A -> B \/ C
-------------------
 A -> B \/ A -> C

Convert to Predicate
--------------------

QQ(s,s',p) ::= s::char_star<flted_10_1615,p>@M & s'=s & s'=s & flted_10_1615=0  
   \/  s::char_star<v_1631,q>@M * QQ(q,s',p) & v_1631!=0 |#|3  

(USING LEMMA_infer for ex13e4a.slk)

   self::QQ<sp,p> <- self::WFSeg<sp>*sp::char_star<0,p>.

================

void while2(ref char_star s1,ref char_star s2)
  requires s1::char_star<_,q>*q::BADS<> * s2::WSS<p>@L 
  ensures s1::WFSeg<s1a>*s1a::char_star<0,s1'>*s1'::BADS<>;
{
  int x=get_char(s2);
  write_char(s1,x);
  s2 = plus_plus_char(s2);
  s1 = plus_plus_char(s1);
  if (x!=0) {
    while2(s1,s2);
  }
}
*/

