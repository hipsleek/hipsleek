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
*/

char *(cstrcat)(char *s1, const char *s2)
  /*@
    requires s1::WFS<> * s2::WFS<> 
    ensures true;
  */
  {
     while (*s1++!='\0') 
       /*@
          requires s1::WFS<> 
          ensures s1::WFSeg<q>*q::char_star<0,s1'>*s1'::BADS<>;
       */
       {
       }
     return s1;
  }

/*
# bug2a.ss

     while (*s1++!='\0') 
          requires s1::WFS<> 
          ensures s1::WFSeg<q>*q::char_star<0,s1'>*s1'::BADS<>;
       {
       }

# is translation below correct?

{ while (true) 
EBase: [][](emp ; (emp ; (s1::WFS{}<>@M[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 2,:(emp ; (emp ; (((s1::WFSeg{}<q>@M[HeapNode1]) * (q::char_star{}<0,s1'>@M[HeapNode1])) * (s1'::BADS{}<>@M[HeapNode1])))) * ([] & true)( FLOW __norm)} 
{
{tmp = s1
s1 = (98, ):__plus_plus_char(s1)
(99, ):if (__get_char_(tmp) != 0) { 
  (99, ):;
} else { 
  (99, ):(100, ):break 
}}
}


# --pcp translation

void while_23_5$char_star~char_star(  char_star tmp,  char_star s1)
{try 
(boolean v_bool_23_1599;
(v_bool_23_1599 = true;
if (v_bool_23_1599) [{(try 
{((tmp = s1;
s1 = {__plus_plus_char$char_star(s1)});
(boolean v_bool_23_1593;
(v_bool_23_1593 = {((int v_int_23_1592;
(v_int_23_1592 = bind tmp to (val_23_1584,next_23_1585) [read] in 
val_23_1584;
(int v_int_23_1591;
v_int_23_1591 = 0)));
neq___$int~int(v_int_23_1592,v_int_23_1591))};
if (v_bool_23_1593) [LABEL! 99,0: ]
else [LABEL! 99,1: throw {,(16,17)=brk_default#E}]
)))}
 catch (19,20)=cnt_default#E  ) 
	LABEL! 104,1: ;
{while_23_5$char_star~char_star(tmp,s1) rec})}]
else []
))
 catch (16,17)=brk_default#E  ) 
	LABEL! 105,1: }

*/
