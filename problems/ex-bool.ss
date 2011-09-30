/* from the Havoc paper */
data content
{
  int val;
}

data dlinknode
{
   content c;
   dlinknode next;
}

ll<S,m,b> == self = null & S = {} & m=0
  or self::dlinknode<c,n> * c::content<i> * n::ll<S1,m-1,b> & S = union (S1,{i}) & b
  or self::dlinknode<c,n> * n::ll<S,m-1,b> & c=null & !b
 inv m>=0 ;

llnull<> == self = null 
    or self::dlinknode<c,n> * n::llnull<> & c=null;

// bool isn't translated correctly into Presburger!
// cannot write b=true or b=false in formula!

/*
void clear_logs(dlinknode loglist)
  requires loglist::ll<S,m,b> & b
  ensures loglist::ll<S1,m,b1> & S1={} & !b1 ;
{
dlinknode ptr = loglist;

if(loglist != null)
 { 
  loglist.c = null ;
  clear_logs(loglist.next);
 }
}
*/






