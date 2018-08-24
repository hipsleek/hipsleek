data message {int val;}

void call0(int arg)
   requires  true
   ensures   true;
{
   foo();
}

//fixed version
void foo(ref message msg)
   requires  msg::message<n> & n>=0
   ensures   msg'::message<0>;
{
  if (msg.val > 0) {
     msg.val = 0;
     call0(msg.val);
  }
}
