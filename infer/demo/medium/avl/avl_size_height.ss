/* AVL Trees */
/* Given Shape -> Infer Size + Height Property */

data node4 {
  int val;
  int height;
  node4 left;
  node4 right;
}

avl<> == self = null
  or self::node4<_, h, p, q> * p::avl<> * q::avl<> & h>=0;


/************************************************************/

/* Return the height of an AVL tree */
int height(node4 x)
  requires x::avl<>
  ensures x::avl<> & res>=0;
{
  if (x == null)
    return 0;
  else
    return x.height;
}


/*  Rotate left */
node4 rotate_left(node4 l, node4 rl, node4 rr)
  requires l::avl<> * rl::avl<> * rr::avl<>
  ensures res::avl<> & res!=null;
{
  node4 tmp;
  int v = 10, h;

  h = height(l) + 1;
  tmp = new node4(v, h, l, rl);
  h = h + 1;
  return new node4(v, h, tmp, rr);
}

/* Rotate right */
node4 rotate_right(node4 ll, node4 lr, node4 r)
  requires ll::avl<> * lr::avl<> * r::avl<>
  ensures res::avl<> & res!=null;
{
  node4 tmp;
  int v = 10, h;

  h = height(r) + 1;
  tmp = new node4(v, h, lr, r);
  h = h + 1;
  return new node4(v, h, ll, tmp);
}

int get_max(int a, int b)
  requires true
  ensures res = max(a, b);
{
  if (a >= b)
    return a;
  else
    return b;
}

/* Double left rotation */
node4 rotate_double_left
  (node4 a, node4 b, node4 c, node4 d, int v1, int v2, int v3)
  requires a::avl<> * b::avl<> * c::avl<> * d::avl<>
  ensures res::avl<> & res!=null;
{
  node4 tmp1, tmp2;
  int h;

  h = get_max(height(a), height(b));
  h = h + 1;
  tmp1 = new node4(v1, h, a, b);

  h = get_max(height(c), height(d));
  h = h + 1;
  tmp2 = new node4(v3, h, c, d);

  h = get_max(height(tmp1), height(tmp2));
  h = h + 1;
  return new node4(v2, h, tmp1, tmp2);
}

/* Double right rotation */
node4 rotate_double_right
  (node4 a, node4 b, node4 c, node4 d, int v1, int v2, int v3)
  requires a::avl<> * b::avl<> * c::avl<> * d::avl<>
  ensures res::avl<> & res!=null;
{
  node4 tmp1, tmp2;
  int h;

  h = get_max(height(a), height(b));
  h = h + 1;
  tmp1 = new node4(v3, h, a, b);

  h = get_max(height(c), height(d));
  h = h + 1;
  tmp2 = new node4(v1, h, c, d);

  h = get_max(height(tmp1), height(tmp2));
  h = h + 1;
  return new node4(v2, h, tmp1, tmp2);
}


/* Build AVL trees */
node4 build_avl(node4 x, node4 y)
  requires x::avl<> * y::avl<> & x != null
  ensures res::avl<> & res!=null;
{
  int v = 0;
  int tmp;

  tmp = x.height;
  tmp = tmp + 1;
  return new node4(v, tmp, x, y);
}

void build_avl2(node4 x, node4 y, node4 z)
  requires y::avl<> * z::avl<> * x::node4<_, _, _, _> & y != null
  ensures  x::avl<> & x!=null;
{
  int tmp;

  x.left = y;
  x.right = z;
  x.height = y.height  + 1;
}

node4 node4_error() 
  requires true 
  ensures false;

/* Insert an element into an AVL tree (using the rotate functions) */
node4 insert(node4 x, int a)
  requires x::avl<>
  ensures res::avl<> & res!=null;
{
  node4 tmp, tmp_null = null;

  if (x == null)
    return new node4 (a, 1, tmp_null, tmp_null);
  else
  {
    if (a <= x.val)
    {
      tmp = x.left;
      x.left = insert(tmp, a);
      // check if we need rotation
      if ((height(x.left) - height(x.right)) == 2)
      {
        if (height(x.left.left) > height(x.left.right))
        {
          return rotate_right(x.left.left, x.left.right, x.right);
        }
        else
        {
          if (height(x.left.left) == (height(x.left.right) - 1))
            return rotate_double_left(x.left.left, x.left.right.left, 
                                x.left.right.right, x.right, 1, 1, 1);
          else
            return node4_error();
        }
      }
      else
        return node4_error();
    }
    else
    {
      tmp = x.right;
      x.right = insert(tmp, a);
      if ((height(x.right) - height(x.left)) == 2)
      {
        if (height(x.right.right) > height(x.right.left))
        {
          return rotate_left(x.left, x.right.left, x.right.right);
        }
        else
        {
          if ((height(x.right.left) - 1) == height(x.right.right))
            return rotate_double_right(x.left, x.right.left.left, 
                        x.right.left.right, x.right.right, 1, 1, 1);
          else
            return node4_error();
        }
      }
      else
        return node4_error();
    }
  }
}

/* Insert an element into an AVL tree (inline version) */
node4 insert_inline(node4 x, int a)
  requires x::avl<>
  ensures res::avl<> & res!=null;
{
  node4 k1, tmp, k2, tmp_null = null;
  int h, hl, hr, hlt;

  if (x == null)
    return new node4(a, 1, tmp_null, tmp_null);
  else
  {
    if (a <= x.val)
    {
      tmp = x.left;
      x.left = insert_inline(tmp, a);
      if ((height(x.left) - height(x.right)) == 2)
      {
        k1 = x.left;
        if (height(k1.left) > height(k1.right))
        {//SRR
          x.left = k1.right;
          h = get_max(height(k1.right), height(x.right));
          k1.right = x;
          h = h + 1;
          x.height = h;
          h = get_max(height(k1.left), h);
          h = h + 1;
          k1.height = h;
          return k1;
        }
        else
        {//DLR
          if (height(k1.left) == (height(k1.right) - 1))
          {
            k2 = k1.right;
            x.left = k2.right;
            k1.right = k2.left;
            hr = height(k2.left);
            k2.left = k1;
            hlt = height(k2.right);
            k2.right = x;

            hl = height(k1.left);
            h = get_max(hl, hr);
            h = h + 1;
            k1.height = h;

            hr = height(x.right);
            h = get_max(hlt, hr);
            h = h + 1;
            x.height = h;

            h = get_max(height(k1), x.height);
            h = h + 1;
            k2.height = h;

              return k2;
          }
          else
              return node4_error();
        }
      }
      else
        return node4_error();
    }
    else  // right branch
    {
      tmp = x.right;
      x.right = insert_inline(tmp, a);
      if ((height(x.right) - height(x.left)) == 2)
      {
        k1 = x.right;
        if (height(k1.right) > height(k1.left))
        {// SLR
          x.right = k1.left;
          hr = height(k1.left);
          k1.left = x;

          hl = height(x.left);
          h = get_max(hr, hl);
          h = h + 1;
          x.height = h;

          hr = height(k1.right);
          h = get_max(height(x), hr);
          h = h + 1;
          k1.height = h;

          return k1;
        }
        else
        { // DRR
          if ((height(k1.left) - 1) == height(k1.right))
          {
            k2 = k1.left;

            x.right = k2.left;
            k1.left = k2.right;
            hr = height(k2.left);
            k2.left = x;
            hlt = height(k2.right);
            k2.right = k1;

            hl = height(x.left);
            h = get_max(hl, hr);
            h = h + 1;
            x.height = h;

            hr = height(k1.right);
            h = get_max(hlt, hr);
            h = h + 1;
            k1.height = h;

            h = get_max(height(x), height(k1));
            k2.height = ++h;

            return k2;
          }
          else
            return node4_error();
        }
      }
      else
        return node4_error();
    }
  }
}

node4 merge(node4 t1, node4 t2)
  case {
    t1=null -> 
      requires t2::avl<> 
      ensures res::avl<>;
    t1!=null -> 
      requires t1::avl<> * t2::avl<> 
      ensures res::avl<>;
  }
{
  if (t1 == null) 
    return t2;
  else {
    node4 tmp = insert(t2, t1.val);
    node4 tmp1 = merge (tmp, t1.left);
    return merge(tmp1, t1.right);
  }
}

