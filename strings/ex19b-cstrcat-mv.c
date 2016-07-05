/*@

 WFS<p> ==
  self::char_star<0,p>
  or self::char_star<v,q>*q::WFS<p> & v!=0 
  inv self!=null;

WFSeg<p> ==
  self=p 
  or self::char_star<v,q>*q::WFSeg<p> & v!=0
  inv true;

BADS<> ==
  self::char_star<v,q>*q::BADS<> 
  inv true;
*/

char *(cstrcat)(char *s1)
 {
     char *s = s1;
     while (*s != '\0')
       /*@

        */
         s++;
     return s1;
 }

/*
int main() {
  char *s1;
  cstrcat(s1);
  return 0;
}
*/
 
/*
# ex19b.s --pip

# (member access s~~>value != 0)

      change to __get_char
        and     __write_char

# should use char_star instead of int_star
# also instead of
    s = (104, ):__pointer_add__int_star__int__(s, 1)}
  need to generate
    s = (104, ):__plus_plus_char(s)}

int_star cstrcat(int_star s1)[]
static EInfer [HP_14,GP_15] EBase: [][](HRel HP_14(s1)) * ([] & true)( FLOW __norm) {EAssume: 2,:(HRel GP_15(s1,res)) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
{
{local: int_star s
int_star s
{s = s1
 while (true) 
 
{
{(99, ):if (member access s~~>value != 0) { 
  (99, ):;
} else { 
  (99, ):(100, ):break 
}
s = (104, ):__pointer_add__int_star__int__(s, 1)}
}
(105, ):return s1}}

}

int main()[]
static 
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 
{
{local: int_star s1
int_star s1
{(106, ):cstrcat(s1)
(107, ):return 0}}
}
int_star __pointer_add__int_star__int__(int_star p, int i)[]
static EBase: [][](emp ; (emp ; (p::int_star{}<val,offset>@M[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 1,:(emp ; (emp ; ((p::int_star{}<val,offset>@M[HeapNode1]) * (res::int_star{}<Anon_13,offset+i>@M[HeapNode1])))) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 

void free(int_star p)[]
static EBase: [][](emp ; (emp ; (p::int_star{}<Anon_16,Anon_17>@M[HeapNode1]))) * ([] & true)( FLOW __norm) {EAssume: 3,:(emp ; (emp ; emp)) * ([] & true)( FLOW __norm)}
dynamic EBase: [][](hfalse) * ([] & false)( FLOW __false) 


*/

