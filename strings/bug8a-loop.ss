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
  ensures src::WFSeg<qq>*qq::char_star<0,src'>*src'::BADS<> * dst::WFSeg<pp>*pp::char_star<0,dst'>*dst'::BADS<>
  or src::WFSeg<src'>*src'::WFS<> * dst::WFSeg<dst'>*dst'::BADS<>;

{
  if (n>0) {
    n--;
    int ch = get_char(src);
    dprint;
    write_char(dst,ch);
    dprint;
    plus_plus_char(src);
    dprint;
    plus_plus_char(dst);
    dprint;
    if (ch == 0) return;
    loop(n,dst,src);
  }
}

/*
# bug8a.ss

  false introduced after write_char

when inv used..

data char_star {
  int val;
  char_star next;
} inv //true;
next = self + 1;

!!! **typechecker.ml#2190:Dprint:[ch,n,dst,src]
dprint(simpl): bug8a-loop.ss:28: ctx:  List of Failesc Context: [FEC(0, 0, 1  [(,0 ); (,1 )])]
 Successful States:
 [
  Label: [(,0 ); (,1 )]
  State:
     hfalse&false&{FLOW,(4,5)=__norm#E}[]
    es_orig_ante: Some(hfalse&false&{FLOW,(4,5)=__norm#E}[])
    es_var_measures 1: Some(MayLoop[]{})
    
  Exc:None
  ]
*/


