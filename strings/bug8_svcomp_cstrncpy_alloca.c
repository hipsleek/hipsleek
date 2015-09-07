#include <stdlib.h>

/*@
WFS<> ==
  self::char_star<0,q>*q::BADS<> 
  or self::char_star<v,q>*q::WFS<> & v!=0 
  inv true;

WFSeg<p> ==
  self=p 
  or self::char_star<v,q>*q::WFSeg<p> & v!=0
  inv true;

BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;

lemma_safe self::WFS<> -> self::BADS<>.
*/

extern int __VERIFIER_nondet_int(void);

char *(cstrncpy)(char *s1, const char *s2, int n)
/*@
    requires s1::BADS<> * s2::WFS<> & n > 0
    ensures true;
*/
 {
     char *dst = s1;
     const char *src = s2;
     /* Copy bytes, one at a time.  */
     while (n > 0)
       /*@
          requires dst::BADS<> * src::WFS<>
          ensures src::WFSeg<qq>*qq::char_star<0,src'>*src'::BADS<> * dst::WFSeg<pp>*pp::char_star<0,dst'>*dst'::BADS<>
               or src::WFSeg<src'>*src'::WFS<> * dst::WFSeg<dst'>*dst'::BADS<>;
       */
     {
         n--;
         if ((*dst++ = *src++) == '\0')
         {
             //@dprint;
             break;
         }
     }
     return s1;
 }
/*============================================================================== wrong
Checking procedure while_32_5$char_star~int~char_star~char_star~char_star~int... 
!!! **typechecker.ml#2190:Dprint:[src,tmp___0,dst,tmp,tmp___1,n]
dprint(simpl): bug8_svcomp_cstrncpy_alloca.c:42: ctx:  List of Failesc Context: [FEC(0, 1, 1  [(,0 ); (,1 ); (,0 ); (,1 ); (,1 )])]
 Escaped States:
 [
  
  Try-Block:125::
  [
   Path: [(,1 ); (,2 ); (,1 )]
   State:  dst::BADS<>@M * src::WFS<>@M&
!(v_bool_32_1782') & n'<=0 & src'=src & tmp___0'=tmp___0 & dst'=dst & 
tmp'=tmp & tmp___1'=tmp___1 & n'=n & v_bool_32_1872'&
{FLOW,(16,17)=brk_default#E}[]
   ];
  ;
  
  ]Successful States:
 [
  Label: [(,0 ); (,1 ); (,0 ); (,1 ); (,1 )]
  State:
     hfalse&false&{FLOW,(4,5)=__norm#E}[]
    es_orig_ante: Some(hfalse&false&{FLOW,(4,5)=__norm#E}[])
    es_cond_path: [1]
    es_var_measures 1: Some(MayLoop[]{})
    
  Exc:None
  ]
================================================================================= correct
Checking procedure while_32_5$char_star~int~char_star~char_star~char_star~int... 
!!! **typechecker.ml#2199:Dprint:[src,tmp___0,dst,tmp,tmp___1,n]
dprint(simpl): bug8_svcomp_cstrncpy_alloca.c:42: ctx:  List of Failesc Context: [FEC(0, 1, 1  [(,0 ); (,1 ); (,0 ); (,1 ); (,1 )])]
 Escaped States:
 [
  
  Try-Block:120::
  [
   Path: [(,1 ); (,2 ); (,1 )]
   State:  dst::BADS<>@M * src::WFS<>@M&
!(v_bool_32_1695') & n'<=0 & src'=src & tmp___0'=tmp___0 & dst'=dst & 
tmp'=tmp & tmp___1'=tmp___1 & n'=n & v_bool_32_1785'&
{FLOW,(16,17)=brk_default#E}[]
   ];
  ;
  
  ]Successful States:
 [
  Label: [(,0 ); (,1 ); (,0 ); (,1 ); (,1 )]
  State:
     dst'::BADS<>@M * src::char_star<tmp___0',src'>@M * src'::BADS<>@M * 
 tmp'::char_star<tmp___0',dst'>@M&
tmp___1'=src & tmp___0'=0 & n'=n-1 & tmp'=dst & 1<=n & dst!=null&
{FLOW,(4,5)=__norm#E}[]
    es_cond_path: [1; 1; 1; 0]
    es_var_measures 1: Some(MayLoop[]{})
    
  Exc:None
  ]


