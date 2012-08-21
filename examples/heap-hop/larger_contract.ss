 

data cell{
  int val;
}


// message definitions

message packet <cell x3> == x3::cell<m> ;
message packet2 <cell x3> == x3::cell<m> ;

 
//contract definitions

contract C { 
  initial   state start { !packet -> ?packet2 -> !packet -> start; 
			      !packet2 -> next;} 
  state next {?packet -> !packet -> !packet -> last;}
  final state last {!packet -> ?packet -> start; 
		    !packet2 -> next;}
 
}

 
 