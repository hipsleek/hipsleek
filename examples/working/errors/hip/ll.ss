/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

void dispose(node x)
  requires x::node<_,_>
  ensures true;

/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

void delete_list(node x)
   requires x::ll<n>
   ensures true;
{
  if (x!=null) {
    delete_list(x.next);
    dispose(x);
  } 
}
	
	
/*ll1<S> == self = null & S = {} 
	or self::node<v, q> * q::ll1<S1> & S = union(S1, {v});*/

/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1   & S=union(S1, {v});*/

/* append two singly linked lists */
void append2(node x, node y)
  requires x::ll<n1> * y::ll<n2> & x!=null // & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<n1+n2>;
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}

void append(node x, node y)
  requires x::ll<n1> * y::ll<n2> & n1>0 // & x!=null // & n1>0 & x != null
  ensures x::ll<n1+n2>;
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

/* return the first element of a singly linked list */
node ret_first(node x)

	requires x::ll<n> * y::ll<m> & n < m 
	ensures x::ll<n>;

{
	return x;
}

/* return the tail of a singly linked list */
node get_next(node x)

	requires x::ll<n> & n > 0
	ensures x::ll<1> * res::ll<n-1>; 

{
  //dprint;
	node tmp = x.next;
    //assume false;
	x.next = null;
	return tmp;
}


/* function to set the tail of a list */
 void set_next(node x, node y)

	requires x::ll<i> * y::ll<j> & i > 0 
	ensures x::ll<j+1>; 

{
	x.next = y;
}

void set_null2(node x)

	requires x::ll<i> & i > 0 
	ensures x::ll<1>;

{
	if (4>3) 
		x.next = null;
	else 
		x.next = null;
}	


/* function to set null the tail of a list */
void set_null(node x)

	requires x::ll<i> & i > 0 
	ensures x::ll<1>;

{
	x.next = null;
    //dprint;
}

/* function to get the third element of a list */
node get_next_next(node x) 

	requires x::ll<n> & n > 1
	ensures res::ll<n-2>;

{
	return x.next.next;
}

/* function to insert a node in a singly linked list */
void insert(node x, int a)
	requires x::ll<n> & n > 0 
	ensures x::ll<n+1>;
{
			//dprint;
      node tmp = null;
	if (x.next == null)
		x.next = new node(a, tmp);
	else 
		insert(x.next, a);
} 

/* function to delete the a-th node in a singly linked list */
void delete(node x, int a)
	requires x::ll<n> & n > a & a > 0 
	ensures x::ll<n - 1>;
{
        if (a == 1)
	{
		//node tmp = x.next.next;
		//x.next = tmp;
                  x.next = x.next.next;
	}
	else
	{
		delete(x.next, a-1);
	}	
}

/*node delete1(node x, int a)
	requires x::ll1<S>  
	ensures res::ll1<S1> & ((a notin S | S=union(S1, {a})) | S = S1);
{
	if (x == null) 
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete1(x.next, a));
	}
}*/

/* function to create a singly linked list with a nodes */
node create_list(int a)
	requires a >= 0 
	ensures res::ll<a>;

{
	node tmp;

	if (a == 0) {
      // assume false;
		return null;
	}
	else {    
		a  = a - 1;
        //    dprint;
		tmp = create_list(a);
        //    dprint;
		return new node (0, tmp);
	}
		
}

/* function to reverse a singly linked list */
void reverse(ref node xs, ref node ys)
	requires xs::ll<n> * ys::ll<m> 
	ensures ys'::ll<n+m> & xs' = null;
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
    //dprint;
		xs.next = ys;
		ys = xs;
		xs = tmp;
    //dprint;
		reverse(xs, ys);
	}
}

/*****************************************/
/*********SMALLROOT EXAMPLES*************/

void list_traverse(node x)
        requires x::ll<n>
        ensures x::ll<n>;
{
        node t;
        if(x != null)   
        {       
              t = x;
              list_traverse(x.next);
        }
}

node list_copy(node x)
        requires x::ll<n>
        ensures x::ll<n> * res::ll<n>;
{         
        node tmp;
        if (x != null) {

               tmp = list_copy(x.next);
               return new node (x.val, tmp) ;
        }
        else
               return null;
}

/*function to insert a node into singly linked list which has sorted tail */
void list_insert(node x, int v)
        requires x::ll<n> & n>0
        ensures x::ll<n+1>;
{
        node tmp;
        if(x.next == null) 
               x.next = new node (v, tmp);
        else
        {
                if(v > x.next.val) {
                        tmp = x.next.next;
                        if (x.next.next == null) {
                               tmp = new node(v,null);
                        }
                        else
                               list_insert(tmp,v);
                        x.next.next = tmp;
                }                 
		else {
                        tmp = x.next;
                        x.next = new node(v,tmp);
                }                        		    
        }
}

/*function to insert a node into a singly linked list being sorted  */
/*NOT WORKING*/
/*void list_insert2(ref node x, int v)
        requires x::ll<n> & n>=0
        ensures x'::ll<n+1>;                                                                                                                                
{
        node tmp;                                                                                                                                
        if(x == null)
               x = new node (v, null); 
        else
        {
                if(v > x.val) { 
                        list_insert2(x.next,v);//fails here                                                                                                  
                }
                else {
                        tmp = x;                                                                                                                     
                        x = new node(v,tmp);                                                                                                                
                }
        }
}*/

/*function to insert a node into a singly linked list being sorted  */
node list_insert3(node x, int v)
        requires x::ll<n> & n>=0
        ensures res::ll<n+1>;                                                                                                                                 
{
        node tmp;                                                                                                                                            
        if(x == null)
               x = new node (v, null);                                                                                                                       
        else
        {
                if(v > x.val) {
                        tmp = list_insert3(x.next,v);                                                                                             
                       x.next = tmp;
                }
                else {
                        tmp = x;                                                                                                                             
                        x = new node(v,tmp);                                                                                                                 
                }
        }
        return x;
}



/*function to remove the first node which has value v in singly linked list*/
void list_remove(node x, int v)
        requires x::ll<n> & n > 0// & x.val != v
        ensures x::ll<m> & m <= n;
{
        if(x.next != null) {
                   if(x.next.val == v) {
                            node tmp = x.next;
                            x.next = x.next.next;
                            dispose(tmp);
                   }
                   else {
                            list_remove(x.next, v);
                   }
        }
}

/*function to remove the first node which has value v in nullable singly linked list*/
node list_remove2(node x, int v)
        requires x::ll<n> & n >= 0
        ensures res::ll<m> & m <= n;                                                                                                                         
{
        node tmp;
        if(x != null) {
                   if(x.val == v) {
                            tmp = x;                                                                                                               
                            x = x.next;                                                                                                            
                            dispose(tmp);                                                                                                                    
                   }
                   else {
                            tmp = list_remove2(x.next, v);
                            x.next = tmp;
                   }
        }
        return x;
}

/*function to remove all nodes which have value v in singly linked list*/
//WRONG
/*void list_filter(node x, int v)
        requires x::ll<n> & n > 0
        ensures x::ll<m> & m <= n;
{
        node tmp;
        if(x.next != null) {
                   if(x.next.val == v){
                            tmp = x.next.next;
                            dispose(x.next);
                            x.next = tmp;
                            if (x.next != null)
                                      list_filter(x.next, v);//wrong here
                   }
                   else {
                            list_filter(x.next, v);
                   }
        }
}*/

/*function to remove all nodes which have value v in nullable singly linked list*/
node list_filter2(node x, int v)
  requires x::ll<n> & n >= 0
  ensures res::ll<m> & m <= n;
{
        node tmp;
        if(x != null) {
                   if(x.val == v){
                            tmp = x.next;
                            dispose(x);
                            x = tmp;
                            x = list_filter2(x,v);
                   }
                   else{
                            tmp = list_filter2(x.next, v);
                            x.next = tmp;
                   }
        }
        return x;
}

/**************************************************************/
/**********************SLAYER (SLL) EXAMPLES***************************/
/*view for list segment*/
lseg<p,n> == self = p & n = 0
        or self::node<_, q> * q::lseg<p, n-1>
  inv n >= 0; 

/*function to create a list segment*/
node create_seg(int n, node t)
       requires n >= 0
       ensures res::lseg<t, n>;
{
       if(n == 0)
           return t;
       else {
           node tmp = create_seg(n-1, t);
           return new node(0, tmp);
       }
}

/*function to destroy a linked list*/
void destroy(node x)
       requires x::ll<n> & n >=0
       ensures true;
{
       if(x != null)
       {
              destroy(x.next);
              dispose(x);
       }
}

/*function to destroy a list segment*/
void destroy_seg(ref node x, node y)
      requires x::lseg<y, n> & n>= 0
      ensures x' = y;//'
{
      node tmp;
      if(x != y)
      {
             tmp = x;
             x = x.next;
             destroy_seg(x, y);
             dispose(tmp);

      }

}

/* function to return the first node being greater than v*/
node find(node x, int v)
      requires x::ll<n> & n >= 0
      ensures res = null or res::node<m,_> & m > v;
{
      if(x == null)
           return null;
      else {
           if(x.val > v)
                 return x;
           else
                 return find(x.next, v);
      }
}


lemma self::lseg<p,n> <- self::lseg<q,a> * q::lseg<p,b> & n = a+b;
/*
void reverse_seg2(ref node x, ref node t)
     requires x::lseg<t,n> * t::lseg<p,m>  & n >= 0//  & x != t
     ensures  x'::lseg<p,n + m >;/'
{
     node tmp;
     if(x == t)
         return;
     if( x.next != t){
          tmp = x;
          x = x.next;
          tmp.next = t;
          t = tmp;
          reverse_seg2(x, t);
     }
 }
*/
/*function to splice 2 linked list*/
void splice (ref node x, node y)
     requires x::ll<n> * y::ll<m>
     ensures x'::ll<m+n>;
{
     if(x == null)
        x = y;
     else {
           if(y != null){
                node nx = x.next;
                node ny = y.next;
                x.next = y;
                splice(nx, ny);
                y.next = nx;
           }
     }
}

/*function to traverse a list segment*/
void traverse_seg(node x, node t)
     requires x::lseg<t,n> & n >= 0
     ensures x::lseg<t,n>;
{
     node tmp;
     if(x != t){
          tmp = x;
          traverse_seg(x.next, t);
     }
}
