data node {
	int val;
    int priority;
    node next;
}


node find_nth2(int j)  requires j>=1 ensures true;

void upgrade_process_prio()
	case {
  1>2 -> ensures true;
  1<=2 -> ensures true;
  }
{
    node proc = find_nth2(0);
}
