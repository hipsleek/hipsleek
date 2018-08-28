data message {int val;}

void call(int arg,ref message msg)
   requires  true
   ensures   msg=msg';
{
   foo(msg);
}

//fixed version
void foo(ref message msg)
   requires  msg::message<n> & n>=0
   ensures   msg'::message<0>;
{
  if (msg.val > 0) {
     msg.val = 0;
     dprint;
     call(msg.val,msg);
     dprint;
  }
}
