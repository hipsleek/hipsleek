/*
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

HeapPred P(char_star s).
HeapPred Q(char_star s).
HeapPred PQ(char_star x, char_star y).

void while1(char_star s1, char_star s2)
/*
  requires s1::WFS<> * s2::BADS<>
  ensures s1::WFSeg<s1'>*s1'::char_star<0,q1>*q1::BADS<> * s2'::BADS<>
          or s1::WFSeg<s1'>*s1'::char_star<c1,q>*q::WFS<>*s2::WFSeg<s2'>*s2'::char_star<c2,qq>*qq::BADS<>;
*/
  infer [
    //P,
    //Q
    PQ
    ,@pure_field
    ,@classic
    ,@size
    ,@term
  ]
  //requires P(s1) * Q(s2)
  //requires s1::WSS<p> * Q(s2)
  requires PQ(s1, s2)
  ensures true;
{
  int x=get_char(s1);
  if (x!=0) {
    int y = get_char(s2);
    if (y==x){
       s1 = plus_plus_char(s1);
       s2 = plus_plus_char(s2); 
       while1(s1,s2);
    }
  }
}

/*
void main () 
  requires true
  ensures true;
{
  int length1, length2;
  if (length1 < 1) length1 = 1;
  if (length2 < 1) length2 = 1;
  char_star str1 = alloc_str(length1);
  char_star str2 = alloc_str(length2);
  //dprint;
  finalize_str(str1, length1-1);
  finalize_str(str2, length2-1);
  //dprint;
  while1(str1, str2);
  //dprint;
}
*/
/*
view PQ<s2:char_star,Anon_1815:char_star,s2_1816:char_star,
 Anon_1817:char_star,Anon_1818:char_star>= 
  EList
    :EBase 
       exists (Impl)[v_1768; v_1784; Anon_1769; 
       Anon_1785](* lbl: *){335}->(exists Anon_1819,Anon_1820,s2_1821,
       Anon_1822,
       Anon_1823: (* lbl: *){335}->self::char_star<v_1768,Anon_1769>@M * 
                                   s2::char_star<v_1784,Anon_1785>@M * 
                                   Anon_1769::PQ<Anon_1819,Anon_1820,s2_1821,Anon_1822,Anon_1823>@M&
       v_1768!=0 & v_1784=v_1768 & Anon_1819=Anon_1785 & 
       Anon_1820=Anon_1815 & s2_1821=s2_1816 & Anon_1822=Anon_1817 & 
       Anon_1823=Anon_1818&{FLOW,(1,28)=__flow#E}[])
    || :EBase 
          exists (Impl)[v_1768; Anon_1769; v_1784; 
          Anon_1785](* lbl: *){336}->self::char_star<v_1768,Anon_1769>@M * 
                                     s2::char_star<v_1784,Anon_1785>@M&
          Anon_1818=Anon_1769 & Anon_1817=Anon_1785 & v_1768!=0 & 
          v_1784!=v_1768&{FLOW,(1,28)=__flow#E}[]
    || :EBase 
          exists (Impl)[v_1768; 
          Anon_1769](* lbl: *){337}->self::char_star<v_1768,Anon_1769>@M&
          s2_1816=s2 & Anon_1815=Anon_1769 & v_1768=0&
          {FLOW,(1,28)=__flow#E}[]
========================================================================
view PQ_size<s2:char_star,s2_1814:char_star,Anon_1815:
char_star,
 Anon_1816:char_star,size_prop:int>= 
  EList
    :EBase 
       (* lbl: *){335}->(exists Anon_1975,s2_1976,Anon_1977,Anon_1978,v_1979,
       v_1980,Anon_1981,Anon_1982,size_1983,size_1984,size_1985,
       size_1986: (* lbl: *){335}->self::char_star<v_1979,Anon_1981>@M * 
                                   s2::char_star<v_1980,Anon_1982>@M * 
                                   Anon_1981::PQ_size<Anon_1975,s2_1976,Anon_1977,Anon_1978,size_1983>@M&
       size_1984=0 & size_1986=size_1984+size_1983 & size_1985=1+size_1984 & 
       size_prop=1+size_1986 & v_1979!=0 & v_1980=v_1979 & 
       Anon_1975=Anon_1982 & s2_1976=s2_1814 & Anon_1977=Anon_1815 & 
       Anon_1978=Anon_1816&{FLOW,(1,28)=__flow#E}[])
    || :EBase 
          (* lbl: *){336}->(exists v_1968,Anon_1969,v_1970,Anon_1971,
          size_1972,size_1973,
          size_1974: (* lbl: *){336}->self::char_star<v_1968,Anon_1969>@M * 
                                      s2::char_star<v_1970,Anon_1971>@M&
          size_1974=0 & size_1972=0 & size_1973=1+size_1972 & 
          size_prop=1+size_1974 & Anon_1816=Anon_1969 & 
          Anon_1815=Anon_1971 & v_1968!=0 & v_1970!=v_1968&
          {FLOW,(1,28)=__flow#E}[])
    || :EBase 
          (* lbl: *){337}->(exists v_1965,Anon_1966,
          size_1967: (* lbl: *){337}->self::char_star<v_1965,Anon_1966>@M&
          size_1967=0 & size_prop=1+size_1967 & s2_1814=s2 & 
          Anon_1816=Anon_1966 & v_1965=0&{FLOW,(1,28)=__flow#E}[])
    view PQ_size{}[]<s2:char_star,s2_1814:char_star,Anon_1815:char_star,
    Anon_1816:char_star,size_prop:int>= 
    inv: size_prop>=0
    
    baga over inv: [([], size_prop>=0)]
    baga over inv (unfolded): [([], size_prop>=0)]
    
    xform: size_prop>=0
    ]

*/
