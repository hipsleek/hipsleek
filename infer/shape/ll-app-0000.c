#include<stdlib.h>
#include<stdio.h>

struct list_el {
   //int val;
   struct list_el *next;
};

typedef struct list_el item;

item* append(item *x, item *y){
  //___sl_plot("simple1");
  item *curr;
  curr = x;
  while (curr->next != NULL) 
    curr = curr->next;
  curr->next = y;
  return x;
}

item* create_list(){
   item *curr, *head;
   int i;

   head = NULL;

   for(i=1;i<=10;i++) {
      curr = (item *)malloc(sizeof(item));
      //curr->val = i;
      curr->next = head;
      head = curr;
   }
   
   item *tmp = head->next;
   free(head);
   head = tmp;
   return head;
}

void main() {
   item *x, *y;
   x = create_list();
   y = create_list();
   ___sl_plot("pre");
   ___sl_summary("infer/shape/ll-app-0000");
   x = append(x, y);
   ___sl_plot("post");
   ___sl_summary("infer/shape/ll-app-0000");
}






