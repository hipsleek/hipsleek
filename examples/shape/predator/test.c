bool nondeterm()
 requires true
 ensures !res or res;

int nondeterm_int()
 requires true
 ensures res = n & n < 1000;

data node {
  int value;
  node next;
}

data list{
  node slist;
  list lnext;
}

data ptr_node{
  node n;
}

data ptr2_node{
  ptr_node pn;
}

ls_node<p> == self=p 
  or self::node<_,q> * q::ls_node<p>  
  inv true;

ls<p> == self=p
  or self::list<n,q> * n::node<_,_> * q::ls<p>
  inv true;

// x::ptr_item<v>*v::item<_>

void merge_single_node(ref ptr2_node dst, ref ptr_node data1)
requires true
ensures true;
{
  node node1 = data1.n;
  data1.n = node1.next;
  node1.next = null;

  dst.pn = node1;
  dst.pn.n = node1.next;
}

void merge_pair(ref ptr_node dst,
                       ref node sub1,
                       ref node sub2)
requires true
ensures true;
{
    // merge two sorted sub-lists into one
    loop_or(dst, sub1, sub2);
}

void loop_or(ref ptr_node dst,ref node sub1, ref node sub2)
requires true
ensures true;
{
  if (sub1 !=null || sub2 !=null ) {
	ptr2_node dst1;
	ptr_node data1_1;
        if (sub2 == null || (sub1 !=null && sub1.value < sub2.value))
            merge_single_node(dst1, data1_1);
        else
            merge_single_node(dst1, data1_1);
	loop_or(dst, sub1, sub2);
    }
}

list seq_sort_core(ref list data1)
requires data1::ls<null>
ensures true;
{
    list dst = null;

    loop_data(data1, dst);

    return dst;
}

void loop_data(ref list data1, ref list dst)
requires data1::ls<null>
ensures true;
{
   if(data1!=null) {
        list next = data1.lnext;
        if (next == null) {
            // take any odd/even padding as it is
            data1.lnext = dst;
            dst = data1;
            return;
        }
	ptr_node tmp;
        // take the current sub-list and the next one and merge them into one
        merge_pair(tmp, data1.slist, next.slist);
        data1.lnext = dst;
        dst = data1;

        // free the just processed sub-list and jump to the next pair
        data1 = next.lnext;
        free_list(next);
        loop_data(data1, dst);
    }
}

void inspect_before(ref list shape)
requires true
ensures true;
{
    /* we should get a list of sub-lists of length exactly one */
    assert(shape!=null);
    loop_shape(shape); 	//FAIL

    /* check the last node separately to make the exercising more fun */
    assert(shape!=null);
    assert(shape.lnext = null);
    assert(shape.slist);
    assert(shape.slist.next = null);
}

void loop_shape(ref list shape)
requires true
ensures true;
{
  if(shape.lnext != null)
  {
	assert(shape != null);
        assert(shape.lnext);
        assert(shape.slist);
        assert(shape.slist.next = null);
	loop_shape(shape.lnext);
  }
}

void inspect_after(ref list shape)
requires true
ensures true;
{
    /* we should get exactly one node at the top level and one nested list */
    assert(shape != null);
    assert(shape.lnext = null);
    assert(shape.slist != null);

    /* the nested list should be zero terminated (iterator back by one node) */
    node pos;
    loop_assert(shape, pos);
}

void loop_assert(ref list shape, ref node pos)
requires true
ensures true;
{
	pos = shape.slist;
	if(pos.next != null){
		assert(pos.next = null);
		loop_assert(shape, pos.next);	
	}
}

int main()
requires true
ensures res = 0;
{
    list data1 = null;
    
    loop1(data1);
    
    if (data1 == null)
        return 0;

    inspect_before(data1);  //assert FAIL

    loop2(data1);

    inspect_after(data1);

    node n = data1.slist;
    free_list(data1);
    loop3(n);

    return 0;
}

void loop1(ref list data1)
requires data1::ls<null>
ensures data1::ls<null>;
{
    if (nondeterm()) {
        node n = malloc_node();
        if (n == null)
            return;

        n.next = null;
        n.value = nondeterm_int();

        list item = malloc_list();
        if (item==null)
            return;

        item.slist = n;
        item.lnext = data1;
        data1 = item;
	loop1(data1);
    }
}

void loop2(ref list data1)
requires data1::ls<null>
ensures data1::ls<null>;
{
 // do O(log N) iterations
    if(data1.lnext !=null){
        data1 = seq_sort_core(data1);
	loop2(data1);
	}
}

void loop3(ref node n)
requires n::ls_node<null>
ensures n=null;
{
   if(n!=null) {
        node snext = n.next;
        free_node(n);
        n = snext;
	loop3(n);
    }
}

node malloc_node ()
 requires true
 ensures res=null or res::node<_, null>;

list malloc_list ()
 requires true
 ensures res=null or res::list<n, null> * n::node<_,_>;

void free_node(ref node n)
 requires n::node<_,_>
 ensures n = null;

void free_list(ref list l)
 requires l::list<_,_>
 ensures l = null;

void form_node(node x, int v1, node n2)
  requires true
  ensures  x::node<v1,n2>;
