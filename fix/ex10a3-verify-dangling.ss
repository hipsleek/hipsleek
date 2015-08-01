
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
void while1(ref str s)
  requires s::WFS<p> 
  ensures s::WFSeg<aaa>*aaa::str<0,bbb> & aaa=s' & bbb=p;
{
  int x=getChar(s);
  if (x!=0) {
    s = incStr(s);
    while1(s);
    dprint;
  }
}

/*
# ex10a3.ss

# What happen to aaa and bbb? Seems to have been eliminated
  below. Can we add an assert_elim_exists here?

!!! **solver.ml#2637:f(b4 elim_exists_es_his):
 (exists flted_40_1612,aaa_1613,bbb_1614,
s_1611: s::str<v_1590,q_1591>@M * s_1611::WFSeg<aaa_1613>@M * 
        aaa_1613::str<flted_40_1612,bbb_1614>@M&
v_bool_43_1521' & s_1607=s & p_1589=p & v_1590!=0 & v=v_1590 & q=q_1591 & 
x'=v & x'!=0 & Anon_12=v_1590 & q_1603=q_1591 & s_1611=q_1603 & 
p_1608=p_1589 & q_1591!=null & flted_40_1612=0 & aaa_1613=s' & 
bbb_1614=p_1608&{FLOW,(4,5)=__norm#E}[]

!!! **solver.ml#2649:f(after elim_exists_es_his): 
 (exists flted_40_1612: s::str<v_1590,q_1591>@M * q_1603::WFSeg<s'>@M * 
                        s'::str<flted_40_1612,p_1608>@M&
v_bool_43_1521' & s_1607=s & p_1589=p & v_1590!=0 & v=v_1590 & q=q_1591 & 
x'=v & x'!=0 & Anon_12=v_1590 & q_1603=q_1591 & p_1608=p_1589 & 
q_1591!=null & flted_40_1612=0&{FLOW,(4,5)=__norm#E}[]



# ex10a3.ss

# why is there inference when we did not have infer_command!

!!! **typechecker.ml#3719:SPECS (before add_pre):
 EBase 
   exists (Expl)[](Impl)[p](ex)[]s::WFS<p>@M&{FLOW,(4,5)=__norm#E}[]
   EBase 
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume 
       ref [s]
       (exists flted_40_65,aaa,
       bbb: s::WFSeg<aaa>@M * aaa::str<flted_40_65,bbb>@M&
       flted_40_65=0 & aaa=s' & bbb=p&{FLOW,(4,5)=__norm#E}[]
!!! **typechecker.ml#3720:NEW SPECS(B4):
 EBase 
   exists (Expl)[](Impl)[p](ex)[]s::WFS<p>@M&{FLOW,(4,5)=__norm#E}[]
   EBase 
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume 
       ref [s]
       (exists flted_40_65,aaa,
       bbb: s::WFSeg<aaa>@M * aaa::str<flted_40_65,bbb>@M&
       flted_40_65=0 & aaa=s' & bbb=p&{FLOW,(4,5)=__norm#E}[]
!!! **typechecker.ml#3722:NEW SPECS(AF):
 EBase 
   exists (Expl)[](Impl)[p](ex)[]s::WFS<p>@M&{FLOW,(4,5)=__norm#E}[]
   EBase 
     emp&MayLoop[]&{FLOW,(4,5)=__norm#E}[]
     EAssume 
       ref [s]
       (exists flted_40_65,aaa,
       bbb: s::WFSeg<aaa>@M * aaa::str<flted_40_65,bbb>@M&
       flted_40_65=0 & aaa=s' & bbb=p&{FLOW,(4,5)=__norm#E}[]

*/

