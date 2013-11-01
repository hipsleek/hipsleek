
struct node {
  int val;
  struct node * next;
};

/*@
ll<> == self=null
  or self::node<_,p>*p::ll<>;
*/

/*@
HeapPred H( node a).
HeapPred G( node a).
*/


int main(struct node* l)
/*@
 requires l::ll<>
  ensures l::ll<>;
*/
{

  int i=0;

  while (l)
    /*
      infer [H,G]
      requires H(l)
      ensures G(l');
     */
    /*@
      requires l::ll<>
      ensures l::ll<> & l'=null;
     */
    {
    l = l->next;
    i++;
  }

  return i;
}


/*
void f_r_878_while_17_2$int~node(  int i_33,  node l)
@ref i_33, l
 rec
static  :EInfer [H,G]
    EBase H(l)&{FLOW,(26,27)=__norm}[]
            EBase emp&MayLoop[]&{FLOW,(1,29)=__flow}[]
                    EAssume ref [i_33;l]
                      
                      G(l')&{FLOW,(26,27)=__norm}[]
                      or G(l')&{FLOW,(12,13)=brk_f_l_17_16}[]
                      
                      
dynamic  EBase hfalse&false&{FLOW,(26,27)=__norm}[]
{(boolean v_bool_17_889;
(v_bool_17_889 = true;
if (v_bool_17_889) [{(try 
{((boolean v_bool_17_885;
(v_bool_17_885 = {bool_of_node___$node(l)};
if (v_bool_17_885) [LABEL! 76,0: ]
else [LABEL! 76,1: throw {,(12,13)=brk_f_l_17_16}]
));
(l = bind l to (val_24_886,next_24_887) [read] in 
next_24_887;
i_33 = {((int v_int_25_888;
v_int_25_888 = 1);
add___$int~int(i_33,v_int_25_888))}))}
 catch (15,16)=cnt_f_l_17_16  ) 
	LABEL! 84,1: ;
{f_r_878_while_17_2$int~node(i_33,l) rec})}]
else []
))}

 */
