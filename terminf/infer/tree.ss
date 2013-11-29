/* An example from the paper 
  "Automated Numeric Abstractions for Heap-Manipulating Programs" */

data tnode { tnode left; tnode right; }

data lnode { tnode tree; lnode next; }

Tree<t> ==
  self = null & t = t0 or
  self::tnode<l, r> * l::Tree<tl> * r::Tree<tr> & t = f(tl, tr)
  //inv s >= 0;
  
TreeList<l> == // s is the number of nodes in the trees linked to by nodes in the stk
  self = null & l = l0 or
  self::lnode<t, nxt> * t::Tree<t> * nxt::TreeList<ln> & l = g(t, ln)  
  //inv s >= 0;
  
lnode push(tnode t, lnode nxt)
  requires t::Tree<st> * nxt::TreeList<sn> & Term
  ensures res::TreeList<l> & l = g(st, sn);
{
  return new lnode(t, nxt);
}

void traverse(tnode root)
  requires root::Tree<s>
  ensures true;
{
  lnode stk;
  lnode tl;
  
  stk = push(root, null);
  while (stk != null) 
    requires stk::TreeList<l> & Term[l]
    ensures stk' = null;
  {
    tl = stk.next;
    if (stk.tree == null) {
      stk = tl; // g(t0, ln) > ln
    } else {
      tl = push(stk.tree.right, tl); //g(tr, ln)
      tl = push(stk.tree.left, tl);  //g(tl, g(tr, ln))
      stk = tl; // g(f(tl, tr), ln) > g(tl, g(tr, ln))
    }
  }
}


g(t0, ln) > ln
ag*t0 + bg*ln + cg > ln
ag*t0 + (bg-1)*ln + cg > 0

g(f(tl, tr), ln) > g(tl, g(tr, ln))
ag*(af*tl + bf*tr + cf) + bg*ln + cg > ag*tl + bg*(ag*tr + bg*ln + cg) + cg 
(ag*af - ag)*tl + (ag*bf - ag*bg)*tr + (bg - bg*bg)*ln + (ag*cf - bg*cg) > 0


