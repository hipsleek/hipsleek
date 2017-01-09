void mayloop ()
  requires MayLoop
  ensures true;

void f(int x) 
  infer [@term]
  requires true
  ensures true;
{
  if (x <= 0) 
    mayloop();
  else
    f(x - 1);
}
/*
# base-1.ss

ti3 branch has the following error message.

Base/Rec Case Splitting:
[	f: [[3] x<=0@ML,[4] 1<=x@R]
]

Context of Verification Failure: 1 File "examples/base-1.ss",Line:8,Col:10
Last Proving Location: 1 File "examples/base-1.ss",Line:13,Col:4

ERROR: at _0:0_0:0 
Message: [TNT Inference]: One of analyzed scc's successors is Unknown.
 Termination Inference Result:
f:  requires emp & MayLoop[]
 ensures emp & true;

 */
