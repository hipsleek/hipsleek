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

void loop(int n, ref char_star dst, ref char_star src)
  requires dst::BADS<> * src::WFS<> & n>=0
  ensures true;
{
    int ch = get_char(src);
    dprint;
    write_char(dst,ch);
    dprint; // false introduced..
}

/*
# bug8b.ss -dre "h_formula_2_mem"

# why did we obtain two q_1670 in baga formula?

(==cvutil.ml#1352==)
h_formula_2_mem@181@180
h_formula_2_mem inp1 : q_1670::BADS<>@M * src::char_star<v_1642,q_1643>@M * q_1643::WFS<>@M * 
 dst'::char_star<v_1671,q_1672>@M
h_formula_2_mem inp2 : n'=n & dst'=dst & src'=src & 0<=n & v_1642!=0 & v=v_1642 & Anon_20=q_1643 & 
 ch'=v & Anon_21=v_1669 & q=q_1670 & q_1670=dst+1 & dst!=null & v_1671=ch' & 
 q_1672=q
h_formula_2_mem inp3 :[]
h_formula_2_mem@181 EXIT: [[q_1670,q_1670,src,q_1643,dst']]

==========================

  false introduced after write_char

when inv used..

data char_star {
  int val;
  char_star next;
} inv //true;
next = self + 1;

!!! **typechecker.ml#2190:Dprint:[ch,n,dst,src]
dprint(simpl): bug8b-loop.ss:24: ctx:  List of Failesc Context: [FEC(0, 0, 1  [])]
 Successful States:
 [
  Label: []
  State:
     hfalse&false&{FLOW,(4,5)=__norm#E}[]
    es_orig_ante: Some(hfalse&false&{FLOW,(4,5)=__norm#E}[])
    es_var_measures 1: Some(MayLoop[]{})
    
  Exc:None
  ]

*/


