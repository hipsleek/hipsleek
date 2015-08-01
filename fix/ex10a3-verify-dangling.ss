
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

simplified --> 

dprint(simpl): ex10a3-verify-dangling.ss:46: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,0 ); (,1 )])]
 Successful States:
 [
  Label: [(,0 ); (,1 )]
  State:
     (exists flted_40_1612: s::str<v_1590,q_1591>@M * q_1603::WFSeg<s'>@M * 
                        s'::str<flted_40_1612,p_1608>@M&
p=p_1608 & flted_40_1612=0 & q_1591=q_1603 & v_1590=x' & q_1603!=null & x'!=0&
{FLOW,(4,5)=__norm#E}[]
    es_cond_path: [1; 0]
    es_var_measures 1: Some(MayLoop[]{})


!!! **cfout.ml#444:elim variables:[Anon_12:int,q:str,v:int,p_1589:str,s_1607:str,v_bool_43_1521':boolean]
!!! **cfout.ml#431:heap2 variables:[v_1590:int,q_1591:str,q_1603:str,flted_40_1612:int,p_1608:str]
!!! **cfout.ml#433:eqmap:emap[{Anon_12,v,v_1590,x'};
{__CONST_Int_0,flted_40_1612};{p,p_1589,p_1608};{q,q_1591,q_1603};{s,s_1607}]

[Anon12->x';v->x';v_1590->x']
[flted_40_1612->0]
[q_1591->q;q_1603->q]
[s_1687->s]

!!! **typechecker.ml#2145:Dprint:[x,p,s]
dprint(orig): ex10a3-verify-dangling.ss:46: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,0 ); (,1 )])]
 Successful States:
 [
  Label: [(,0 ); (,1 )]
  State:
     (exists flted_40_1612: 
    s::str<v_1590,q_1591>@M * q_1603::WFSeg<s'>@M * 
    s'::str<flted_40_1612,p_1608>@M & flted_40_1612=0 & q_1591!=null 
    & p_1608=p_1589 & q_1603=q_1591 & Anon_12=v_1590 & x'!=0 & x'=v 
   & q=q_1591 & v=v_1590 & v_1590!=0 & p_1589=p 
   & s_1607=s & v_bool_43_1521'&{FLOW,(4,5)=__norm#E}[]
    es_cond_path: [1; 0]
    es_var_measures 1: Some(MayLoop[]{})
    
  Exc:None
  ]
 
dprint(simpl): ex10a3-verify-dangling.ss:46: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,0 ); (,1 )])]
 Successful States:
 [
  Label: [(,0 ); (,1 )]
  State:
     (exists flted_40_1612: 
    s::str<v_1590,q_1591>@M * q_1603::WFSeg<s'>@M * 
    s'::str<flted_40_1612,p_1608>@M
    & flted_40_1612=0 & q_1591=q_1603 & v_1590=x' 
    & p=p_1608 & q_1603!=null & x'!=0&
{FLOW,(4,5)=__norm#E}[]
    es_cond_path: [1; 0]
    es_var_measures 1: Some(MayLoop[]{})
    
  Exc:None
  ]


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




*/

