data node {
	node next;	
}

/* view for singly linked circular lists */
cll<p, n> == self = p & n = 0
	or self::node<r> * r::cll<p, n-1> & self != p  & n > 0;


/* function to create a singly linked list with a nodes */
node create_list(int a)
	requires a > 0 
	ensures res::ll<a>;

{
	node tmp;

	if (a == 1) {
		return new node(null);
	}
	else {    
		tmp = create_list(a-1);
		return new node (tmp);
	}
		
}
