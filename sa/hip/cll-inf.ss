/* circular lists */
/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for singly linked circular lists */
cll<p> == self = p	or self::node<_, r> * r::cll<p> & self != p;

hd<> == self = null	or self::node<_, r> * r::cll<self> ;

HeapPred H1(node x).
HeapPred H2(node x, node y).
 
void insert(node x, int v)
	infer [H1]	requires H1(x)  ensures H1(x);
{
    x.next = new node(v, x.next);	
}
 
int count_rest(node rest, node h)
	infer [H2] requires H2(rest, h) ensures H2(rest, h); 
{
	if (rest == h) return 0; 
	else return 1+count_rest(rest.next, h);
}

int count(node x)
	infer [H1] requires H1(x) ensures H1(x);
{
	if (x == null) return 0;
	else return count_rest(x.next, x) + 1;
}
/*
void delete(ref node x)
	infer [H1] requires H1(x) ensures H1(x');
{
	if (x.next == x) x = null;
	else x.next = x.next.next;
}
*/
/*

node test() 
	requires true
	ensures true;
{
	node null_tmp = null; 
	node tmp = new node(10, null_tmp);

	//assert tmp'::cll<_, 1>;

	//assert tmp'::node<_, r> * r::cll<r, 0> assume;

	tmp.next = tmp;

	node tmp2 = new node(20, tmp.next);
	tmp.next = tmp2;

	//assert tmp'::hd<2>;

	return tmp;
}


*/