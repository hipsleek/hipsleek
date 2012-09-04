data node {
  int val;
  node next;
}

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).

void reverse(ref node x, ref node y)
  infer[H1,H2,G1,G2]
  requires H1(x)*H2(y)
     ensures G1(x,x')*G2(y,y');
{
	if(x!= null){
		node tmp = x.next;
		x.next = y;
		y = x;
		x = tmp;
		reverse(x,y);
	}
}

/*
 H1(x) * H2(y) & x!=null --> x::node<val_17_526',next_17_527'> * HP_545(next_17_527')
 H1(x) * H2(y) & x!=null  --> x::node<val_18_528',next_18_529'> * HP_549(next_18_529')
 H1(x) * H2(y) * x::node<val_18_562,y> & x!=null & y'=x & x'=tmp_19' --> H1(x') * H2(y')
 H1(x) * H2(y) * x::node<val_18_562,y> * G1(tmp_566,x') * G2(x,y') & x!=null --> G1(x,x') * G2(y,y')
 H1(x) * H2(y) & x'=x & y'=y & x'=null --> G1(x,x') * G2(y,y')

--after simplify
 H1(x) & x!=null --> x::node<val_17_526',next_17_527'> * HP_545(next_17_527')
 H1(x) & x!=null --> x::node<val_18_528',next_18_529'> * HP_549(next_18_529') //duplicate
 H1(x) * x::node<val_18_562,y> & x!=null --> H1(tmp_19') * H2(x)
 H1(x) * H2(y) * x::node<val_18_562,y> * G1(tmp_566,x') * G2(x,y') & x!=null --> G1(x,x') * G2(y,y')
 H1(x) * H2(y) & x=null --> G1(x,x) * G2(y,y)

 */
