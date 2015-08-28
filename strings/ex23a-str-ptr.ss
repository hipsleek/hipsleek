/*
in prelude.ss
data char_star {
  int val;
  char_star next;
}
*/

data char_str {
  int val;
  char_str next;
} inv self+1=next;


WSS<p> ==
  self::WFSeg<q>*q::char_str<0,p> 
  inv self!=null;

WFSeg<p> ==
  self=p 
  or self::char_str<v,q>*q::WFSeg<p> & v!=0
  inv true;

char_star plus_plus_str(char_star x)
requires x::char_str<_,q>@L & Term[] 
ensures  res=q ;

int get_str(char_star x)
  requires x::char_str<v,_>@L & Term[]
  ensures res=v;

/*
BADS<> ==
  self::char_str<v,q>*q::BADS<> 
  inv true;
*/

HeapPred P(char_str x).

void while1(ref char_str s)
/*
  infer [P,@classic]
  requires P(s)
  ensures true;
*/
  requires s::WSS<p> 
  ensures s::WFSeg<s'>*s'::char_str<0,p> ;
{
  int x=get_str(s);
  if (x!=0) {
    s = plus_plus_str(s);
    while1(s);
  }
}

/*
# ex23a.ss

# Need to fix the parser for hip to accept invariant 
for data structure.

Parsing file "ex23a-str-ptr.ss" by default parser...
File "ex23a-str-ptr.ss", line 12, characters 13-17
 --error: Stream.Error("EOF expected after [hprogn] (in [hprog])")
 at:
!!! **main.ml#1180:WARNING : Logging not done on finalizecaught

Exception occurred: Stream.Error("EOF expected after [hprogn] (in [hprog])")
Error3(s) detected at main 



*/
