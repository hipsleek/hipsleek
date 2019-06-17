data node {
   int val;
}

void swap(node x, node y)
requires x::node<a> * y::node<b>
ensures x::node<b> * y::node<a>;
{
  int t = x.val;
  x.val = y.val + 3; 
  y.val = t;
}

// {(((int t;
// t = bind x to (val_9_1873) [read] in 
// val_9_1873);
// {(int v_int_10_1880;
// (v_int_10_1880 = {((int v_int_10_1879;
// (v_int_10_1879 = bind y to (val_10_1874) [read] in 
// val_10_1874;
// (int v_int_10_1878;
// v_int_10_1878 = 3)));
// add___$int~int(v_int_10_1879,v_int_10_1878))};
// bind x to (val_10_1881) [write] in 
// val_10_1881 = v_int_10_1880))});
// bind y to (val_11_1882) [write] in 
// val_11_1882 = t)}
// RlFRead(x.val, a)
// [RlFRead(y.val, b)
// [RlFrameData(y, y)
// [RlFrameData(x, x)
// [RlAssign (int b =  (-1*a)+(2*t))
// [RlSkip
// []]]]]]
