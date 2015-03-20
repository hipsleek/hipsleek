

data LinkedList
{
char head;

LinkedList tail;
}
 char LinkedList_getFirst(LinkedList _this)
{
  return this_head;
}

LinkedList LinkedList_getTail(LinkedList _this)
{
  return this_tail;
}



data Infix2Postfix
{

}
 LinkedList Infix2Postfix_buildExpression(int n)
{
  LinkedList exp = null;
  
  int i = 1;
  while (i <= n) {
    if (i <= n - 1)
      exp = new LinkedList(')', exp);
    exp = new LinkedList(')', exp);
    exp = new LinkedList('b', exp);
    exp = new LinkedList('+', exp);
    exp = new LinkedList('a', exp);
    exp = new LinkedList('(', exp);
    if (i <= n - 1)
      exp = new LinkedList('*', exp);
    i++;
  }
  
  
  int i = 1;
  while (i < n) {
    exp = new LinkedList('(', exp);
    i++;
  }
  
  return exp;
}

LinkedList Infix2Postfix_toPostfix(LinkedList infix)
{
  LinkedList operators = null;
  LinkedList operands = null;
  while (infix != null) {
    char c = LinkedList_getFirst();
    switch (c) {
      case '(':
        break;
      case '+':
      case '-':
      case '*':
      case '/':
        operators = new LinkedList(c, operators);
        break;
      case ')':
        operands = new LinkedList(LinkedList_getFirst(), operands);
        operators = LinkedList_getTail();
        break;
      default:
        operands = new LinkedList(c, operands);
    }
    infix = LinkedList_getTail();
  }
  LinkedList postfix = null;
  while (operands != null) {
    postfix = new LinkedList(LinkedList_getFirst(), postfix);
    operands = LinkedList_getTail();
  }
  return postfix;
}

void Infix2Postfix_main(String[] args)
{
  LinkedList infix = Infix2Postfix_buildExpression(args.length);
  LinkedList postfix = Infix2Postfix_toPostfix(infix);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;