#include <stdlib.h>
#include <stdio.h>
struct node {
	int data;
	struct node *next;
};
struct row {
	struct node *data;
	struct row *next;
};

struct node *add_data(struct node *head, int x)
{
	struct node *new;
	new = (struct node *)malloc(sizeof(struct node));
	new->data = x;
	new->next = NULL;
	if (head == NULL) {
		head = new;
	} else {
		struct node *tmp = head;
		while (tmp->next != NULL)
			tmp = tmp->next;
		tmp->next = new;
	}
	return head;
}
struct row *add_row(struct row *head, struct node *x)
{
	struct row *new;
	new = (struct row *)malloc(sizeof(struct row));
	new->data = x;
	new->next = NULL;
	if (head == NULL) {
		head = new;
	} else {
		struct row *tmp = head;
		while (tmp->next != NULL)
			tmp = tmp->next;
		tmp->next = new;
	}
	return head;

}
void print(struct row *head, int n, int m)
{
	int i, j;
	for (i = 0; i < n; i++) {
		struct node *cols  = head->data;
		for (j = 0; j < m; j++) {
			printf("%d ", cols->data);
			cols = cols->next;
		}
		head = head->next;
		printf("\n");
	}
}
int main(void)
{
	struct row *rows = NULL;
	int n = 4, m = 4, i, j;
	for (i = 0; i < n; i++) {
		struct node *cols = NULL;
		for (j = 0; j < m; j++)
			cols = add_data(cols, i + j);
		rows = add_row(rows, cols);
	}
	print(rows, n, m);
	return 0;

}
