data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, r> * r::ll<n-1> inv n>=0;

/* view for a sorted list */
sll<n, sm, lg> == self = null & n = 0 & sm <= lg 
	or self::node<qmin, q> * q::sll<n-1, qs, ql> & qmin <= qs & ql <= lg & sm <= qmin  
	inv n >= 0 & sm <= lg;


int read_int() {
	int i1 = -1;
	java {
	try {
		java.io.InputStreamReader stdin =
				new java.io.InputStreamReader(System.in);
		java.io.BufferedReader console =
				new java.io.BufferedReader(stdin);

		String s1 = console.readLine();
		i1 = Integer.parseInt(s1);
	}
	catch (Exception e) {}
	}
	return i1;
}

node read_list() {
	node head = null, tmp = null;

	java {

		System.out.println("Enter the elements of your list, -1 to finish.");

		while (true) {
			System.out.print("Element = ");
			int n = read_int();
			if (n == -1) break;
			
			if (head == null) {
				head = new node(n, null);
				tmp = head;
			}
			else {
				tmp.next = new node(n, null);
				tmp = tmp.next;
			}
		}
	}

	return head;	
}


void print_list(node list) 
	requires list::ll<n>
	ensures true;
{
	if (list != null) {
		java { System.out.println(list.val); }
		print_list(list.next);
	}
}

/* transform a normal singly linked list in a sorted list */
node insertion_sort(node x)
	requires x::ll<n> & x!=null
	ensures res::sll<n, _, _>;
{
	if (x.next != null) {
		x.next = insertion_sort(x.next);
		node tmp = insert2(x.next, x);
		return tmp;
	}
	else {
		return x;
	}
}

node insert2(node x, node vn)
	requires x::sll<n, sm, lg> *  vn::node<v, _>
	ensures res::sll<n+1, mi, ma> & mi=min(v, sm) & ma=max(v, lg);
{
	if (x==null) {
		vn.next = null;
		return vn;
	}
	else if (vn.val <= x.val) {
		vn.next = x;
		return vn;
	}
	else {
		x.next = insert2(x.next, vn);
		return x;
	}
}


void main() {
	node list = read_list();

	assume list'::ll<n>;

	java { System.out.println("Original list"); }

	print_list(list);

	list = insertion_sort(list);

	java { System.out.println("Sorted list"); }
	print_list(list);
}
