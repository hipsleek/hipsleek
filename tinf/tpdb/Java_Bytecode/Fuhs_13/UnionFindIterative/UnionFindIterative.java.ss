

data UnionFindIterative
{
UnionFindIterative parent;
}
 void UnionFindIterative_makeSet(UnionFindIterative _this)
{
  this_parent = this;
}

UnionFindIterative UnionFindIterative_find(UnionFindIterative _this)
{
  UnionFindIterative candidate = this;
  while (candidate.parent != candidate) {
    candidate = candidate.parent;
  }
  return candidate;
}

void UnionFindIterative_union(UnionFindIterative _this, UnionFindIterative y)
{
