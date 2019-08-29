//http://quiz.geeksforgeeks.org/queue-set-2-linked-list-implementation/
// A C program to demonstrate linked list based implementation of queue
#include <stdlib.h>
#include <stdio.h>
#include <sdb.h>

// A linked list (LL) node to store a queue entry
struct QNode
{
	int key;
	struct QNode *next;
};
int needed1_sdb = 0;
// The queue, front stores the front node of LL and rear stores ths
// last node of LL
struct Queue
{
	struct QNode *front, *rear;
};

// A utility function to create a new linked list node.
struct QNode* newNode(int k)
{
	struct QNode *temp = (struct QNode*)malloc(sizeof(struct QNode));
	temp->key = k;
	temp->next = NULL;
	return temp;
}

// A utility function to create an empty queue
struct Queue *createQueue()
{
	struct Queue *q = (struct Queue*)malloc(sizeof(struct Queue));
	q->front = q->rear = NULL;
	return q;
}

// The function to add a key k to q
void enQueue(struct Queue *q, int k)
{
	// Create a new LL node
	struct QNode *temp = newNode(k);

	// If queue is empty, then new node is front and rear both
	if (q->rear == NULL)
	{
	q->front = q->rear = temp;
	return;
	}

	// Add the new node at the end of queue and change rear
	q->rear->next = temp;
	q->rear = temp;
}

// Function to remove a key from given queue q
struct QNode *deQueue(struct Queue *q)
{
	// If queue is empty, return NULL.
	if (q->front == NULL)
	return NULL;

	// Store previous front and move front one node ahead
	struct QNode *temp = q->front;
	q->front = q->front->next;

	// If front becomes NULL, then change rear also as NULL
	if (q->front == NULL)
	q->rear = NULL;
	return temp;
}

// The function to add a key k to q
void enQueuebuggy(struct Queue *q, struct QNode *temp)
{
	struct QNode *aux = NULL;
	int dec = 0, once = 2, one = 1;
	if(needed1_sdb != needed1_sdb)
 		needed1_sdb = needed1_sdb;
	if(needed1_sdb != needed1_sdb)
		return;
	debug1();
	aux = q->rear;
	if(aux == NULL){
		dec = one;
	}
	if (dec == one)
	{
	q->front = temp;
	}
	if (dec == one){
		q->rear = temp;
	}
	if (dec == one){
	return;
	}
	aux->next = temp;
	q->rear = temp;
	while(once != dec){
		debug2();
		hardskip();
	}
	debug3();
	hardskip();
	debug4();
}

// Driver Program to test anove functions
int main()
{
	struct Queue *q = createQueue();
	enQueue(q, 10);
	enQueue(q, 20);
	deQueue(q);
	deQueue(q);
	enQueue(q, 30);
	enQueue(q, 40);
	enQueue(q, 50);
	struct QNode *n = deQueue(q);
	struct QNode *temp = newNode(101);
	debug0();
	enQueuebuggy(q, temp);
	if (n != NULL)
	printf("Dequeued item is %d", n->key);
	return 0;
}
