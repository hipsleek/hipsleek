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

char *(loop2)(char *s1, const char *s2)
  /*@
    requires s1::char_star<_,q> * q::BADS<> * s2::WFS<>
    ensures s2::WFSeg<qq>*qq::char_star<0,res>*res::BADS<>;
  */
  {
     while ((*s1++ = *s2++) != '\0')
       /*@
          requires s1::char_star<_,q> * q::BADS<> * s2::WFS<>  
          ensures s2::WFSeg<qq>*qq::char_star<0,s2'>*s2'::BADS<> * s1'::BADS<>;
       */
         ;   
     return s2;
  }

char* new_str()
  /*@
     requires emp
     ensures res::WFS<>;
  */
 {}

/*
# bug2d.c

--pip

char_star loop2(char_star s1, char_star s2)[]
static EBase: [][](emp ; (emp ; (((s1::char_star{}<Anon_11,q>@M[HeapNode1]) * (q::BADS{}<>@M[HeapNode1])) * (s2::WFS{}<>@M[HeapNode1])))) * ([] & true)( FLOW __norm) {EAssume: 1,:(emp ; (emp ; (((s2::WFSeg{}<qq>@M[HeapNode1]) * (qq::char_star{}<0,res>@M[HeapNode1])) * (res::BADS{}<>@M[HeapNode1])))) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
{
{local: char_star tmp,int tmp___0,char_star tmp___1
char_star tmp
int tmp___0
char_star tmp___1
{ while (true) 
EBase: [][](emp ; (emp ; (((s1::char_star{}<Anon_12,q>@M[HeapNode1]) * (q::BADS{}<>@M[HeapNode1])) * (s2::WFS{}<>@M[HeapNode1])))) * ([] & true)( FLOW __norm) {EAssume: 2,:(emp ; (emp ; (((s2::WFSeg{}<qq>@M[HeapNode1]) * (qq::char_star{}<0,s2'>@M[HeapNode1])) * (s2'::BADS{}<>@M[HeapNode1])))) * ([] & true)( FLOW __norm)} 
{
{tmp = s1
s1 = (100, ):__plus_plus_char(s1)
tmp___1 = s2
s2 = (103, ):__plus_plus_char(s2)
tmp___0 = __get_char_(tmp___1)
(106, ):__write_char(tmp, tmp___0)
(107, ):if (tmp___0 != 0) { 
  (107, ):;
} else { 
  (107, ):(108, ):break 
}}
}
(110, ):return s2}}
}

*/
