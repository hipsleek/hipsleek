/*
 char *(cstrcat)(char *s1, const char *s2)
 {
     char *s = s1;
     while (*s != '\0')
         s++;
     while ((*s++ = *s2++) != '\0')
         ;               
     return s1;
 }

int main() {
  char *s1;
  char *s2;
  cstrcat(s1, s2);
  return 0;
}
*/

data str {
  int val;
  str next;
}

WFS<p> ==
  self::str<0,p> 
  or self::str<v,q>*q::WFS<p> & v!=0 
  inv self!=null;

WFSeg<p> ==
  self=p 
  or self::str<v,q>*q::WFSeg<p> & v!=0
  inv true;

BADS<> ==
  self::str<v,q>*q::BADS<> 
  inv true;

str incStr(str x)
  requires x::str<_,q>@L & Term[]
  ensures  res=q ;

void assignStr(str x,int v)
  requires x::str<_,q> & Term[]
  ensures  x::str<v,q> ;

int getChar(str x)
  requires x::str<v,q>@L & Term[]
  ensures res=v;
 
/*
     while (*s != '\0')
         s++;
 no guarantee it reaches the end of string ..
*/
relation PP(str s, str a, str b, str c).
void while1(ref str s)
  infer [PP]
  requires s::WFS<p> 
  ensures s::WFSeg<a>*a::str<0,b> & PP(s,p,s',b) ;
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
  }
}

/*
# ex10a1.ss

 infer [PP]
  requires s::WFS<p> 
  ensures s::WFSeg<a>*a::str<0,b> & PP(s,p,s',b) ;

Expects
=======
  s'=a  & b=p

GOT:
!!! **pi.ml#777:>>POST:  s!=null & s'!=null & p=b

****** Before putting into fixcalc*******
pre_vars: s,p
post_vars: s',b
*************************************
formula:  ((b=p & s=s' & s'!=null) | 
  (exists(q_1596:q_1596!=null & PP(q_1596,p,s',b)) & s!=null))
*************************************

!!! **fixcalc.ml#1032:Input of fixcalc: :PP:={[NODs,NODp] -> [NODPRIs,NODb] -> []: (NODb=NODp && NODs=NODPRIs && NODPRIs>0 ||  (exists (NODq_1596:NODq_1596>0 && PP(NODq_1596,NODp,NODPRIs,NODb)))  && NODs>0)
};
bottomupgen([PP], [2], SimHeur);
!!! **fixcalc.ml#390:svls (orig):[PP,p,s',b,s]
!!! **fixcalc.ml#391:svls (from parse_fix):[s,s',p,b]
!!! **fixcalc.ml#1060:Result of fixcalc (parsed): :[ s!=null & s'!=null & p=b]
!!! **pi.ml#775:>>>>>>>>>>> (bef postprocess): <<<<<<<<<
!!! **pi.ml#776:>>REL POST:  PP(s,p,s',b)
!!! **pi.ml#777:>>POST:  s!=null & s'!=null & p=b
!!! **pi.ml#778:>>REL PRE :  true
!!! **pi.ml#779:>>PRE :  true

*/
