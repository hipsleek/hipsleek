/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

/* append two singly linked lists */

void append2(node x, node y)
  requires x::ll<n1> * y::ll<n2> & n1>0 // & x!=null // & n1>0 //x!=null // & n1>0 & x != null
  ensures x::ll<m> & m=n1+n2;
{    
  if (x==null) {
    assert true;
    //dprint;
  }
  else if (x.next == null) x.next = y;
  else
           append2(x.next, y);
}

int foo()
  requires false
  ensures res=1;
{ return 1;
}

/*
# ex3-ll.ss

Warning: False precondition detected in procedure foo$
 with context:   hfalse&false&{FLOW,(4,5)=__norm#E}[]

# to add false context of pre-condition for hip
  and later sleek.

# Find location of this pre-cond warning and add it to
    !Globals.false_ctx_line_list

chin@loris-7:~/hg/sl_imm/fix$ grep "false contexts" ../ *.ml
../maingui.ml:    print_string ("\n"^(string_of_int (List.length !Globals.false_ctx_line_list))^" false contexts at: ("^
../main.ml:    print_string_quiet ("\n"^(string_of_int (List.length !Globals.false_ctx_line_list))^" false contexts at: ("^
../main.ml:    print_string_quiet ("\n"^(string_of_int (List.length !Globals.false_ctx_line_list))^" false contexts at: ("^
c
*/
